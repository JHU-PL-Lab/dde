open Core
open Z3
open Grammar

exception Unreachable

module AtomKey = struct
  module T = struct
    type t = atom [@@deriving hash, sexp, compare]

    (* let hash = function
         | LabelResAtom (_, st) -> State.hash_lstate st
         | ExprResAtom (_, st) -> State.hash_estate st
         | LabelStubAtom st -> State.hash_lstate st
         | ExprStubAtom st -> State.hash_estate st
         | _ as a -> hash a

       let compare a b =
         match (a, b) with
         | LabelResAtom (_, st1), LabelStubAtom st2
         | LabelStubAtom st1, LabelResAtom (_, st2) ->
             State.compare_lstate st1 st2
         | ExprResAtom (_, st1), ExprStubAtom st2
         | ExprStubAtom st1, ExprResAtom (_, st2) ->
             State.compare_estate st1 st2
         | _, _ -> compare a b *)
  end

  include T
  include Comparable.Make (T)
end

module ResKey = struct
  module T = struct
    type t = res [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

module E = struct
  module T = struct
    type t = Expr.expr

    let compare = Expr.compare
    let sexp_of_t e = e |> Expr.ast_of_expr |> AST.to_sexpr |> Sexp.of_string
    let t_of_sexp s = failwith "unimplemented"
    let hash e = e |> Expr.ast_of_expr |> AST.hash
  end

  include T
  include Comparable.Make (T)
end

let res_to_id = Hashtbl.create (module ResKey)
let atom_to_id = Hashtbl.create (module AtomKey)
let fresh_id = ref (-1)

let idr r =
  Format.sprintf "P%d"
    (Hashtbl.find_or_add res_to_id r ~default:(fun () ->
         incr fresh_id;
         !fresh_id))

let ida a =
  let data =
    (* any well-formed pairs of labeled result and stub is
       such that the latter must have already been visited
       by the time we get to the former *)
    match a with
    | LabelResAtom (_, st) -> (
        match Hashtbl.find atom_to_id (LabelStubAtom st) with
        | Some id -> Some id
        (* so if a stub is not found, then `a` is not involved
           in any cycles *)
        | None -> Hashtbl.find atom_to_id a)
    | ExprResAtom (_, st) -> (
        match Hashtbl.find atom_to_id (ExprStubAtom st) with
        | Some id -> Some id
        | None -> Hashtbl.find atom_to_id a)
    | _ -> Hashtbl.find atom_to_id a
  in
  let id =
    match data with
    | Some id ->
        (* still add an entry; won't change the table if
           key already exists *)
        ignore (Hashtbl.add atom_to_id ~key:a ~data:id);
        id
    | None ->
        incr fresh_id;
        Hashtbl.add_exn atom_to_id ~key:a ~data:!fresh_id;
        !fresh_id
  in
  Format.sprintf "P%d" id

let id_to_decl = Hashtbl.create (module String)
let ctx = mk_context []
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
let ( >== ) e1 e2 = Arithmetic.mk_ge ctx e1 e2
let ( <== ) e1 e2 = Arithmetic.mk_le ctx e1 e2

let ( |. ) vars body =
  Quantifier.expr_of_quantifier
    (Quantifier.mk_forall_const ctx vars body None [] [] None None)

let solver = Solver.mk_solver_s ctx "HORN"
let chcs = Hash_set.create (module E)
let list_of_chcs () = Hash_set.to_list chcs
let entry_decl = ref None

let find_or_add aid sort =
  match Hashtbl.find id_to_decl aid with
  | Some p -> p
  | None ->
      let p = zdecl aid [ sort ] bsort in
      Hashtbl.add_exn id_to_decl ~key:aid ~data:p;
      p

let reset () =
  Hashtbl.clear res_to_id;
  Hashtbl.clear atom_to_id;
  Hashtbl.clear id_to_decl;
  Hash_set.clear chcs;
  Solver.reset solver;
  entry_decl := None;
  fresh_id := -1

let rec cond pis =
  if List.is_empty pis then ([], ztrue)
  else
    let conjs =
      List.foldi pis
        ~f:(fun i conjs (r, b) ->
          let c = zconst (Format.sprintf "c%d" i) bsort in
          let p = zdecl (idr r) [ bsort ] bsort in
          p <-- [ c ] &&& (c === zbool b) &&& conjs)
        ~init:ztrue
    in
    (List.mapi pis ~f:(fun i _ -> zconst (Format.sprintf "c%d" i) bsort), conjs)

and chcs_of_atom ?(sort = isort) ?(pis = []) a =
  match a with
  | IntAtom i ->
      let cond_quants, cond_body = cond pis in
      let pa = find_or_add (ida a) isort in
      let body = pa <-- [ zint i ] in
      Hash_set.add chcs
        (if List.is_empty cond_quants then body
         else cond_quants |. cond_body --> body)
  | BoolAtom b ->
      let cond_quants, cond_body = cond pis in
      let pa = find_or_add (ida a) bsort in
      let body = pa <-- [ zbool b ] in
      Hash_set.add chcs
        (if List.is_empty cond_quants then body
         else cond_quants |. cond_body --> body)
  | OpAtom op -> (
      match op with
      | PlusOp (r1, r2)
      | MinusOp (r1, r2)
      | EqualOp (r1, r2)
      | AndOp (r1, r2)
      | OrOp (r1, r2) ->
          let pid, id1, id2 = (ida a, idr r1, idr r2) in
          let is_int_arith =
            match op with PlusOp _ | MinusOp _ -> true | _ -> false
          in
          let zop =
            match op with
            | PlusOp _ -> ( +++ )
            | MinusOp _ -> ( --- )
            | EqualOp _ -> ( === )
            | AndOp _ -> ( &&& )
            | OrOp _ -> ( ||| )
            | _ -> raise Unreachable
          in
          let p = zdecl pid [ (if is_int_arith then isort else bsort) ] bsort in
          let param_sort =
            match op with
            | PlusOp _ | MinusOp _ | EqualOp _ -> isort
            | _ -> bsort
          in
          let p1, p2 =
            (zdecl id1 [ param_sort ] bsort, zdecl id2 [ param_sort ] bsort)
          in
          let const1, const2 =
            (zconst "r1" param_sort, zconst "r2" param_sort)
          in
          (* don't use `add_exn` as we allow duplicates *)
          ignore
            ( Hashtbl.add id_to_decl ~key:pid ~data:p,
              Hashtbl.add id_to_decl ~key:id1 ~data:p1,
              Hashtbl.add id_to_decl ~key:id2 ~data:p2 );
          let cond_quants, cond_body = cond pis in
          chcs_of_res ~sort:param_sort r1 ~pis;
          chcs_of_res ~sort:param_sort r2 ~pis;
          Hash_set.add chcs
            (const1 :: const2 :: cond_quants
            |. (p1 <-- [ const1 ] &&& (p2 <-- [ const2 ]) &&& cond_body)
               --> (p <-- [ zop const1 const2 ]))
      | NotOp r' ->
          let pid, rid = (ida a, idr r') in
          let p = zdecl pid [ bsort ] bsort in
          let p' = zdecl rid [ bsort ] bsort in
          let const = zconst "r" bsort in
          ignore
            ( Hashtbl.add id_to_decl ~key:pid ~data:p,
              Hashtbl.add id_to_decl ~key:rid ~data:p' );
          let cond_quants, cond_body = cond pis in
          chcs_of_res ~sort:bsort r' ~pis;
          Hash_set.add chcs
            ((const :: cond_quants |. (p' <-- [ const ]) &&& cond_body)
            --> (p <-- [ znot const ])))
  | LabelResAtom (r', _) | ExprResAtom (r', _) ->
      chcs_of_res ~sort r' ~pis;

      let aid = ida a in
      let rid = idr r' in
      let pr = Hashtbl.find_exn id_to_decl rid in
      let rdom = FuncDecl.get_domain pr in
      let pa = zdecl aid rdom bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      let r = zconst "r" (List.hd_exn rdom) in
      Hash_set.add chcs ([ r ] |. (pr <-- [ r ]) --> (pa <-- [ r ]))
      (* *point self at the same decl *)
      (* ignore
         @@ Hashtbl.add id_to_decl ~key:(ida a)
              ~data:(Hashtbl.find_exn id_to_decl (idr r')) *)
  | PathCondAtom (((r, b) as pi), r0) ->
      (* generate CHCs for current path condition using
         the previous path conditions *)
      chcs_of_res ~sort r ~pis;
      chcs_of_res ~sort r0 ~pis:(pi :: pis);
      (* *point self at the same decl *)
      Hashtbl.add_exn id_to_decl ~key:(ida a)
        ~data:(Hashtbl.find_exn id_to_decl (idr r0))
  | FunAtom _ | LabelStubAtom _ | ExprStubAtom _ -> ()
  | RecordAtom _ -> failwith "unimplemented"
  | ProjectionAtom _ -> failwith "unimplemented"
  | InspectionAtom _ -> failwith "unimplemented"

and chcs_of_res ?(sort = isort) ?(pis = []) r =
  let rid = idr r in
  List.iter r ~f:(fun a ->
      chcs_of_atom a ~sort ~pis;
      let aid = ida a in
      match Hashtbl.find id_to_decl aid with
      | Some pa ->
          let adom = FuncDecl.get_domain pa in
          let p = zdecl rid adom bsort in
          (* the root assertion is always P0 *)
          if String.(rid = "P0") then entry_decl := Some p;
          ignore (Hashtbl.add id_to_decl ~key:rid ~data:p);
          let consta = zconst "r" (List.hd_exn adom) in
          (* TODO: add flag to leave all path conditions out *)
          let cond_quants, cond_body = cond pis in
          Hash_set.add chcs
            (consta :: cond_quants
            |. (pa <-- [ consta ] &&& cond_body) --> (p <-- [ consta ]))
      | None -> (
          match a with
          | ExprStubAtom _ | LabelStubAtom _ ->
              let cond_quants, cond_body = cond pis in
              (* need to know from a parent context (binop) what
                 sort this constant needs to be *)
              let r = zconst "r" sort in
              let pa = zdecl aid [ sort ] bsort in
              let pr = zdecl rid [ sort ] bsort in
              Hash_set.add chcs
                (r :: cond_quants
                |. (pa <-- [ r ] &&& cond_body) --> (pr <-- [ r ]))
          | _ ->
              Format.printf "debug: %a\n" Grammar.pp_atom a;
              failwith "resatom non-labeled"))

let test =
  [
    LabelResAtom
      ([ OpAtom (PlusOp ([ IntAtom 1 ], [ LabelStubAtom (0, []) ])) ], (0, []));
  ]

let chcs_of_test _ =
  chcs_of_res test;
  let chcs = Hash_set.to_list chcs in
  Format.printf "CHCs:\n";
  List.iter ~f:(fun chc -> Format.printf "%s\n" (Z3.Expr.to_string chc)) chcs;
  Format.printf "\nres_to_id:\n";
  Core.Hashtbl.iteri
    ~f:(fun ~key ~data ->
      Format.printf "key: %a\ndata: %d\n" Grammar.pp_res key data)
    res_to_id;
  Format.printf "\natom_to_id:\n";
  Core.Hashtbl.iteri
    ~f:(fun ~key ~data ->
      Format.printf "key: %a\ndata: %d\n" Grammar.pp_atom key data)
    atom_to_id;
  reset ()
