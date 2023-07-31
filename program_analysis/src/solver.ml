open Core
open Z3
open Grammar

exception Unreachable

module AtomKey = struct
  module T = struct
    type t = atom [@@deriving hash, sexp, compare]
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
let ( >>> ) e1 e2 = Arithmetic.mk_gt ctx e1 e2
let ( <== ) e1 e2 = Arithmetic.mk_le ctx e1 e2
let ( <<< ) e1 e2 = Arithmetic.mk_lt ctx e1 e2

let ( |. ) vars body =
  Quantifier.expr_of_quantifier
    (Quantifier.mk_forall_const ctx vars body None [] [] None None)

let solver = Solver.mk_solver_s ctx "HORN"
let chcs = Hash_set.create (module E)
let list_of_chcs () = Hash_set.to_list chcs
let entry_decl = ref None

let find_or_add aid sort =
  match Hashtbl.find id_to_decl aid with
  (* TODO: does the same leaf atom needs to be assigned different predicates? *)
  | Some pa -> pa
  | None ->
      let pa = zdecl aid [ sort ] bsort in
      Hashtbl.add_exn id_to_decl ~key:aid ~data:pa;
      pa

let reset () =
  Hashtbl.clear res_to_id;
  Hashtbl.clear atom_to_id;
  Hashtbl.clear id_to_decl;
  Hash_set.clear chcs;
  Solver.reset solver;
  entry_decl := None;
  fresh_id := -1

(** can assume good form due to call to `eval_assert` *)
let chcs_of_assert p (r : Interpreter.Ast.result_value_fv) =
  let ri = zconst "r" isort in
  let rb = zconst "r" bsort in
  match r with
  | BoolResultFv b -> Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> zbool b)
  | VarResultFv -> Hash_set.add chcs ([ rb ] |. (p <-- [ rb ]) --> rb === ztrue)
  | OpResultFv op -> (
      match op with
      | EqOpFv (IntResultFv i) ->
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> (ri === zint i))
      | GeOpFv (IntResultFv i) ->
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> (ri >== zint i))
      | GtOpFv (IntResultFv i) ->
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> (ri >>> zint i))
      | LeOpFv (IntResultFv i) ->
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> (ri <== zint i))
      | LtOpFv (IntResultFv i) ->
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> (ri <<< zint i))
      | NotOpFv ->
          Hash_set.add chcs ([ rb ] |. (p <-- [ rb ]) --> (rb === zfalse))
      | _ -> raise Unreachable)
  | _ -> raise Unreachable

let rec cond pis =
  if List.is_empty pis then ([], ztrue)
  else
    let conjs =
      List.foldi pis
        ~f:(fun i conjs (r, b) ->
          let c = zconst (Format.sprintf "c%d" i) bsort in
          let pr = zdecl (idr r) [ bsort ] bsort in
          pr <-- [ c ] &&& (c === zbool b) &&& conjs)
        ~init:ztrue
    in
    (List.mapi pis ~f:(fun i _ -> zconst (Format.sprintf "c%d" i) bsort), conjs)

and chcs_of_atom ?(pis = []) a =
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
      | OrOp (r1, r2)
      | GeOp (r1, r2)
      | GtOp (r1, r2)
      | LeOp (r1, r2)
      | LtOp (r1, r2) ->
          let aid, rid1, rid2 = (ida a, idr r1, idr r2) in
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
            | GeOp _ -> ( >== )
            | GtOp _ -> ( >>> )
            | LeOp _ -> ( <== )
            | LtOp _ -> ( <<< )
            | _ -> raise Unreachable
          in
          let pa =
            zdecl aid [ (if is_int_arith then isort else bsort) ] bsort
          in
          let param_sort =
            match op with
            | PlusOp _ | MinusOp _ | EqualOp _ | GeOp _ | GtOp _ | LeOp _
            | LtOp _ ->
                isort
            | _ -> bsort
          in
          let pr1, pr2 =
            (zdecl rid1 [ param_sort ] bsort, zdecl rid2 [ param_sort ] bsort)
          in
          let r1_, r2_ = (zconst "r1" param_sort, zconst "r2" param_sort) in
          (* don't use `add_exn` as we allow duplicates *)
          ignore
            ( Hashtbl.add id_to_decl ~key:aid ~data:pa,
              Hashtbl.add id_to_decl ~key:rid1 ~data:pr1,
              Hashtbl.add id_to_decl ~key:rid2 ~data:pr2 );
          let cond_quants, cond_body = cond pis in
          chcs_of_res r1 ~pis;
          chcs_of_res r2 ~pis;
          Hash_set.add chcs
            (r1_ :: r2_ :: cond_quants
            |. (pr1 <-- [ r1_ ] &&& (pr2 <-- [ r2_ ]) &&& cond_body)
               --> (pa <-- [ zop r1_ r2_ ]))
      | NotOp r ->
          let aid, rid = (ida a, idr r) in
          let pa = zdecl aid [ bsort ] bsort in
          let pr = zdecl rid [ bsort ] bsort in
          let r_ = zconst "r" bsort in
          ignore
            ( Hashtbl.add id_to_decl ~key:aid ~data:pa,
              Hashtbl.add id_to_decl ~key:rid ~data:pr );
          let cond_quants, cond_body = cond pis in
          chcs_of_res r ~pis;
          Hash_set.add chcs
            ((r_ :: cond_quants |. (pr <-- [ r_ ]) &&& cond_body)
            --> (pa <-- [ znot r_ ])))
  | LabelResAtom (r, _) | ExprResAtom (r, _) ->
      (* derive Z3 sort for labeled result/stub pair from the sort of
         the concrete disjuncts, which is sound on any proper,
         terminating programs. *)
      let sort =
        List.fold r ~init:None ~f:(fun t a ->
            (* this may assign an ID for stub to be later inherited by
               its enclosing res atom but will trigger a lookup failure
               (caught) at stub's (non-existent) Z3 decl *)
            chcs_of_atom a ~pis;
            match Hashtbl.find id_to_decl (ida a) with
            | Some pa ->
                (* TODO: assert that all disjuncts are of the same type *)
                Some (pa |> FuncDecl.get_domain |> List.hd_exn)
            | None -> t (* should hit this case at least once *))
        |> function
        | Some t -> t
        | None -> raise Unreachable
      in
      let aid = ida a in
      let pa = zdecl aid [ sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      let rid = idr r in
      let pr = zdecl rid [ sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:rid ~data:pr);
      (* most of this is repetitive work, but necessary *)
      chcs_of_res r ~pis;
      let r_ = zconst "r" sort in
      Hash_set.add chcs ([ r_ ] |. (pr <-- [ r_ ]) --> (pa <-- [ r_ ]))
  | PathCondAtom (((r, b) as pi), r0) ->
      (* generate CHCs for current path condition using
         the previous path conditions *)
      chcs_of_res r ~pis;
      chcs_of_res r0 ~pis:(pi :: pis);
      (* point self at the same decl *)
      ignore
        (Hashtbl.add id_to_decl ~key:(ida a)
           ~data:(Hashtbl.find_exn id_to_decl (idr r0)))
  | FunAtom _ | LabelStubAtom _ | ExprStubAtom _ -> ()
  | RecordAtom _ -> failwith "unimplemented"
  | ProjectionAtom _ -> failwith "unimplemented"
  | InspectionAtom _ -> failwith "unimplemented"
  | AssertAtom (r1, r2) ->
      chcs_of_res r1 ~pis;
      let p = Hashtbl.find_exn id_to_decl (idr r1) in
      chcs_of_assert p r2

and chcs_of_res ?(pis = []) r =
  let rid = idr r in
  List.iter r ~f:(fun a ->
      chcs_of_atom a ~pis;
      let aid = ida a in
      let cond_quants, cond_body = cond pis in
      match Hashtbl.find id_to_decl aid with
      | Some pa ->
          let dom = FuncDecl.get_domain pa in
          let pr = zdecl rid dom bsort in
          (* the root assertion is always P0 *)
          if String.(rid = "P0") then entry_decl := Some pr;
          ignore (Hashtbl.add id_to_decl ~key:rid ~data:pr);
          let r = zconst "r" (List.hd_exn dom) in
          (* TODO: add flag to leave all path conditions out *)
          Hash_set.add chcs
            (r :: cond_quants |. (pa <-- [ r ] &&& cond_body) --> (pr <-- [ r ]))
      | None -> (
          match a with
          | LabelStubAtom _ | ExprStubAtom _ | AssertAtom _ -> ()
          | _ -> failwith "resatom non-labeled"))

(* let test =
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
     reset () *)
