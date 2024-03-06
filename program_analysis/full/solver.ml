(** Translation from analysis results to Constrained Horn Clauses (CHCs)
    per paper Section 5.2.2 *)

open Core
open Z3
open Utils
open Exns

let ctx = mk_context []

(* Convenience shorthands *)
let isort = Arithmetic.Integer.mk_sort ctx
let bsort = Boolean.mk_sort ctx
let zint i = Arithmetic.Integer.mk_numeral_i ctx i
let zbool b = Boolean.mk_val ctx b
let ztrue = zbool true
let zfalse = zbool false
let znot e = Boolean.mk_not ctx e
let zconst s sort = Expr.mk_const_s ctx s sort
let zdecl s dom ran = FuncDecl.mk_func_decl_s ctx s dom ran
let ( --> ) hyp concl = Boolean.mk_implies ctx hyp concl
let ( <-- ) f args = Expr.mk_app ctx f args
let ( === ) e1 e2 = Boolean.mk_eq ctx e1 e2
let ( &&& ) e1 e2 = Boolean.mk_and ctx [ e1; e2 ]
let ( ||| ) e1 e2 = Boolean.mk_or ctx [ e1; e2 ]
let ( +++ ) e1 e2 = Arithmetic.mk_add ctx [ e1; e2 ]
let ( --- ) e1 e2 = Arithmetic.mk_sub ctx [ e1; e2 ]
let ( *** ) e1 e2 = Arithmetic.mk_mul ctx [ e1; e2 ]
let ( >== ) e1 e2 = Arithmetic.mk_ge ctx e1 e2
let ( >>> ) e1 e2 = Arithmetic.mk_gt ctx e1 e2
let ( <== ) e1 e2 = Arithmetic.mk_le ctx e1 e2
let ( <<< ) e1 e2 = Arithmetic.mk_lt ctx e1 e2

let ( |. ) vars body =
  Quantifier.expr_of_quantifier
    (Quantifier.mk_forall_const ctx vars body None [] [] None None)

module Rids_key = struct
  module T = struct
    type t = Res.t [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Aids_key = struct
  module T = struct
    type t = Atom.t [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Chcs_key = struct
  module T = struct
    open Z3

    type t = Expr.expr

    let compare = Expr.compare
    let sexp_of_t e = e |> Expr.ast_of_expr |> AST.to_sexpr |> Sexp.of_string
    let t_of_sexp s = failwith "unimplemented"
  end

  include T
  include Comparable.Make (T)
end

(** State monad threaded through the translation *)
module State = struct
  module T = struct
    type state = {
      rids : string Map.M(Rids_key).t;
      aids : string Map.M(Aids_key).t;
      chcs : Core.Set.M(Chcs_key).t;
      decls : FuncDecl.func_decl String.Map.t;
      cnt : int;
      entry_decl : FuncDecl.func_decl Option.t;
    }

    type 'a t = state -> 'a * state

    let return (a : 'a) : 'a t = fun st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun st ->
      let a, st' = m st in
      f a st'

    let map = `Define_using_bind
    let get () : state t = fun st -> (st, st)

    let get_rid r : string t =
     fun ({ rids; cnt; _ } as st) ->
      match Map.find rids r with
      | Some rid -> (rid, st)
      | None ->
          let rid = Format.sprintf "P%d" cnt in
          let rids' = Map.add_exn rids ~key:r ~data:rid in
          (rid, { st with rids = rids'; cnt = cnt + 1 })

    let get_aid a : string t =
     fun ({ aids; cnt; _ } as st) ->
      let data =
        (* Any well-formed cycle is such that the stub must
           have already been visited before the labeled result *)
        match a with
        | Atom.LResAtom (_, st) -> (
            match Map.find aids (LStubAtom st) with
            | Some id -> Some id
            (* If no stub , then `a` doesn't start a cycle *)
            | None -> Map.find aids a)
        | EResAtom (_, st) -> (
            match Map.find aids (EStubAtom st) with
            | Some id -> Some id
            | None -> Map.find aids a)
        | _ -> Map.find aids a
      in
      match data with
      | Some id ->
          let aids' = Map.add_exn (Map.remove aids a) ~key:a ~data:id in
          (id, { st with aids = aids' })
      | None ->
          let aid = Format.sprintf "P%d" cnt in
          let aids' = Map.add_exn aids ~key:a ~data:aid in
          (aid, { st with aids = aids'; cnt = cnt + 1 })

    let add_chc e : unit t =
     fun ({ chcs; _ } as st) -> ((), { st with chcs = Core.Set.add chcs e })

    let find_decl aid sort : FuncDecl.func_decl t =
     fun ({ decls; _ } as st) ->
      match Map.find decls aid with
      | Some pa -> (pa, st)
      | None ->
          let pa = zdecl aid [ sort ] bsort in
          let decls' = Map.add_exn decls ~key:aid ~data:pa in
          (pa, { st with decls = decls' })

    let add_decl aid decl : unit t =
     fun ({ decls; _ } as st) ->
      match Map.find decls aid with
      | Some _ -> ((), st)
      | None -> ((), { st with decls = Map.add_exn decls ~key:aid ~data:decl })

    let get_decl aid : FuncDecl.func_decl t =
     fun ({ decls; _ } as st) -> (Map.find_exn decls aid, st)

    let set_entry decl : unit t =
     fun st -> ((), { st with entry_decl = Some decl })

    let run (m : 'a t) =
      m
        {
          rids = Map.empty (module Rids_key);
          aids = Map.empty (module Aids_key);
          chcs = Core.Set.empty (module Chcs_key);
          decls = String.Map.empty;
          cnt = 0;
          entry_decl = None;
        }
  end

  include T
  include Monad.Make (T)
end

open State
open State.Let_syntax

(** Generate CHCs from a letassert. *)
let chcs_of_assert r1 (r2 : Interp.Ast.Res_fv.t) : unit T.t =
  let%bind r1id = get_rid r1 in
  let%bind p = get_decl r1id in
  let ri = zconst "r" isort in
  let rb = zconst "r" bsort in
  match r2 with
  | BoolResFv b -> add_chc ([ ri ] |. (p <-- [ ri ]) --> zbool b)
  | VarResFv id' -> add_chc ([ rb ] |. (p <-- [ rb ]) --> rb === ztrue)
  | EqResFv (v1, IntResFv i)
  | GeResFv (v1, IntResFv i)
  | GtResFv (v1, IntResFv i)
  | LeResFv (v1, IntResFv i)
  | LtResFv (v1, IntResFv i) -> (
      let op =
        match r2 with
        | EqResFv _ -> ( === )
        | GeResFv _ -> ( >== )
        | GtResFv _ -> ( >>> )
        | LeResFv _ -> ( <== )
        | LtResFv _ -> ( <<< )
        | _ -> raise Unreachable
      in
      match v1 with
      | VarResFv _ -> add_chc ([ ri ] |. (p <-- [ ri ]) --> op ri (zint i))
      | ProjResFv (VarResFv _, Ident x) ->
          let%bind p =
            let r1_hd = List.hd_exn r1 in
            match r1_hd with
            | Atom.RecAtom _ ->
                let%bind r1_hd_id = get_aid r1_hd in
                get_decl (r1_hd_id ^ "_" ^ x)
            | LResAtom ([ a ], _) ->
                let%bind aid = get_aid a in
                get_decl (aid ^ "_" ^ x)
            | _ -> raise Unreachable
          in
          add_chc ([ ri ] |. (p <-- [ ri ]) --> op ri (zint i))
      | _ -> raise Unreachable)
  | NotResFv _ -> add_chc ([ rb ] |. (p <-- [ rb ]) --> (rb === zfalse))
  | _ -> raise Bad_assert

(** Generate CHCs from path conditions *)
let rec cond pis : 'a T.t =
  if List.is_empty pis then return ([], ztrue)
  else
    let%bind conjs =
      List.foldi pis ~init:(return ztrue) ~f:(fun i conjs (r, b) ->
          let%bind conjs = conjs in
          let c = zconst (Format.sprintf "c%d" i) bsort in
          let%bind rid = get_rid r in
          let pr = zdecl rid [ bsort ] bsort in
          return (pr <-- [ c ] &&& (c === zbool b) &&& conjs))
    in
    return
      ( List.mapi pis ~f:(fun i _ -> zconst (Format.sprintf "c%d" i) bsort),
        conjs )

(** Generate CHCs from value atoms *)
and chcs_of_atom ?(pis = []) ?(stub_sort = isort)
    ?(p = Core.Set.empty (module St)) a : unit T.t =
  match a with
  | Atom.IntAtom i ->
      let%bind cond_quants, cond_body = cond pis in
      let%bind aid = get_aid a in
      let%bind pa = find_decl aid isort in
      let body = pa <-- [ zint i ] in
      add_chc
        (if List.is_empty cond_quants then body
         else cond_quants |. cond_body --> body)
  | BoolAtom b ->
      let%bind cond_quants, cond_body = cond pis in
      let%bind aid = get_aid a in
      let%bind pa = find_decl aid bsort in
      let body = pa <-- [ zbool b ] in
      add_chc
        (if List.is_empty cond_quants then body
         else cond_quants |. cond_body --> body)
  | PlusAtom (r1, r2)
  | MinusAtom (r1, r2)
  | MultAtom (r1, r2)
  | EqAtom (r1, r2)
  | AndAtom (r1, r2)
  | OrAtom (r1, r2)
  | GeAtom (r1, r2)
  | GtAtom (r1, r2)
  | LeAtom (r1, r2)
  | LtAtom (r1, r2) ->
      let%bind aid = get_aid a in
      let%bind r1id = get_rid r1 in
      let%bind r2id = get_rid r2 in
      let is_int_arith =
        match a with
        | PlusAtom _ | MinusAtom _ | MultAtom _ -> true
        | _ -> false
      in
      let zop =
        match a with
        | PlusAtom _ -> ( +++ )
        | MinusAtom _ -> ( --- )
        | MultAtom _ -> ( *** )
        | EqAtom _ -> ( === )
        | AndAtom _ -> ( &&& )
        | OrAtom _ -> ( ||| )
        | GeAtom _ -> ( >== )
        | GtAtom _ -> ( >>> )
        | LeAtom _ -> ( <== )
        | LtAtom _ -> ( <<< )
        | _ -> raise Unreachable
      in
      let pa = zdecl aid [ (if is_int_arith then isort else bsort) ] bsort in
      let param_sort =
        match a with
        | PlusAtom _ | MinusAtom _ | MultAtom _ | EqAtom _ | GeAtom _ | GtAtom _
        | LeAtom _ | LtAtom _ ->
            isort
        | _ -> bsort
      in
      let pr1, pr2 =
        (zdecl r1id [ param_sort ] bsort, zdecl r2id [ param_sort ] bsort)
      in
      let r1_, r2_ = (zconst "r1" param_sort, zconst "r2" param_sort) in
      let%bind () = add_decl aid pa in
      let%bind () = add_decl r1id pr1 in
      let%bind () = add_decl r2id pr2 in
      let%bind cond_quants, cond_body = cond pis in
      let%bind () = chcs_of_res r1 ~pis ~stub_sort:param_sort ~p in
      let%bind () = chcs_of_res r2 ~pis ~stub_sort:param_sort ~p in
      add_chc
        (r1_ :: r2_ :: cond_quants
        |. (pr1 <-- [ r1_ ] &&& (pr2 <-- [ r2_ ]) &&& cond_body)
           --> (pa <-- [ zop r1_ r2_ ]))
  | NotAtom r ->
      let%bind aid = get_aid a in
      let%bind rid = get_rid r in
      let pa = zdecl aid [ bsort ] bsort in
      let pr = zdecl rid [ bsort ] bsort in
      let r_ = zconst "r" bsort in
      let%bind () = add_decl aid pa in
      let%bind () = add_decl rid pr in
      let%bind cond_quants, cond_body = cond pis in
      let%bind () = chcs_of_res r ~pis ~stub_sort:bsort ~p in
      add_chc
        ((r_ :: cond_quants |. (pr <-- [ r_ ]) &&& cond_body)
        --> (pa <-- [ znot r_ ]))
  | LResAtom (r, st) ->
      (* Derive Z3 sort for labeled result/stub pair from the sort of
         the concrete disjuncts, which is sound on any proper,
         terminating programs. *)
      let p = Core.Set.add p (St.Lstate st) in
      let%bind sort =
        match%bind
          List.fold r ~init:(return None) ~f:(fun t a ->
              (* This may assign an ID for stub to be later inherited by
                 its enclosing res atom but will trigger a lookup failure
                 (caught) at stub's (non-existent) Z3 decl *)
              let%bind () = chcs_of_atom a ~pis ~stub_sort ~p in
              let%bind aid = get_aid a in
              let%bind { decls; _ } = get () in
              match Map.find decls aid with
              | Some pa ->
                  let%bind _ = t in
                  return (Some (pa |> FuncDecl.get_domain |> List.hd_exn))
              | None -> t)
        with
        | Some t -> return t
        | None -> raise Unreachable
      in
      let%bind aid = get_aid a in
      let pa = zdecl aid [ sort ] bsort in
      let%bind () = add_decl aid pa in
      let%bind rid = get_rid r in
      let pr = zdecl rid [ sort ] bsort in
      let%bind () = add_decl rid pr in
      (* Most of this is repetitive work, but necessary *)
      let%bind () = chcs_of_res r ~pis ~stub_sort ~p in
      let r_ = zconst "r" sort in
      add_chc ([ r_ ] |. (pr <-- [ r_ ]) --> (pa <-- [ r_ ]))
  | EResAtom (r, st) ->
      let p = Core.Set.add p (St.Estate st) in
      let%bind sort =
        match%bind
          List.fold r ~init:(return None) ~f:(fun t a ->
              let%bind () = chcs_of_atom a ~pis ~stub_sort ~p in
              let%bind aid = get_aid a in
              let%bind { decls; _ } = get () in
              match Map.find decls aid with
              | Some pa ->
                  let%bind _ = t in
                  return (Some (pa |> FuncDecl.get_domain |> List.hd_exn))
              | None -> t)
        with
        | Some t -> return t
        | None ->
            Format.printf "%a\n" Res.pp r;
            raise Unreachable
      in
      let%bind aid = get_aid a in
      let pa = zdecl aid [ sort ] bsort in
      let%bind () = add_decl aid pa in
      let%bind rid = get_rid r in
      let pr = zdecl rid [ sort ] bsort in
      let%bind () = add_decl rid pr in
      let%bind () = chcs_of_res r ~pis ~stub_sort ~p in
      let r_ = zconst "r" sort in
      add_chc ([ r_ ] |. (pr <-- [ r_ ]) --> (pa <-- [ r_ ]))
  | PathCondAtom (((r, _) as pi), r0) -> (
      (* Generate CHCs for current path condition using
         the previous path conditions *)
      let%bind () = chcs_of_res r ~pis ~stub_sort ~p in
      let%bind () = chcs_of_res r0 ~pis:(pi :: pis) ~stub_sort ~p in
      (* Point self at the same decl *)
      let%bind r0id = get_rid r0 in
      let%bind { decls; _ } = get () in
      match Map.find decls r0id with
      | Some decl ->
          let%bind aid = get_aid a in
          add_decl aid decl
      | None -> return ())
  | FunAtom _ -> return ()
  | LStubAtom ((l, s) as st) ->
      let%bind aid = get_aid a in
      let pa = zdecl aid [ stub_sort ] bsort in
      let%bind () = add_decl aid pa in
      if not (Core.Set.mem p (St.Lstate st)) then
        let r_ = zconst "r" stub_sort in
        add_chc ([ r_ ] |. (pa <-- [ r_ ]))
      else return ()
  | EStubAtom ((e, s) as st) ->
      let%bind aid = get_aid a in
      let pa = zdecl aid [ stub_sort ] bsort in
      let%bind () = add_decl aid pa in
      if not (Core.Set.mem p (St.Estate st)) then
        let r_ = zconst "r" stub_sort in
        add_chc ([ r_ ] |. (pa <-- [ r_ ]))
      else return ()
  | AssertAtom (id, r1, r2) ->
      let%bind () = chcs_of_res r1 ~pis ~stub_sort ~p in
      chcs_of_assert r1 r2
  (* Records are good for demoing that pure demand analysis
     subsumes shape analysis *)
  | RecAtom _ -> return ()
  | ProjAtom _ | InspAtom _ ->
      Format.printf "%a\n" Atom.pp a;
      raise Unreachable

(** Generate CHCs from value results *)
and chcs_of_res ?(pis = []) ?(stub_sort = isort)
    ?(p = Core.Set.empty (module St)) r : unit T.t =
  let%bind rid = get_rid r in
  List.fold r ~init:(return ()) ~f:(fun acc a ->
      let%bind () = chcs_of_atom a ~pis ~stub_sort ~p in
      let%bind aid = get_aid a in
      let%bind cond_quants, cond_body = cond pis in
      let%bind { decls; _ } = get () in
      match Map.find decls aid with
      | Some pa ->
          let%bind _ = acc in
          let dom = FuncDecl.get_domain pa in
          let pr = zdecl rid dom bsort in
          (* At if conditions, the root assertion is always P0 *)
          let%bind () =
            if String.(rid = "P0") then set_entry pr else return ()
          in
          let%bind () = add_decl rid pr in
          let r = zconst "r" (List.hd_exn dom) in
          add_chc
            (r :: cond_quants |. (pa <-- [ r ] &&& cond_body) --> (pr <-- [ r ]))
      | None -> acc)

(** Entrypoint to verification of analysis result *)
let verify_result r =
  let solver = Solver.mk_solver_s ctx "HORN" in
  let (), { chcs; _ } = run (chcs_of_res r) in
  let chcs = Core.Set.elements chcs in
  Z3.Solver.add solver chcs;
  match Z3.Solver.check solver [] with
  | SATISFIABLE -> ()
  | UNSATISFIABLE ->
      raise (Verification_error "Unsat: result doesn't satisfy constraint")
  | UNKNOWN -> raise (Verification_error "Z3 gives unknown")
