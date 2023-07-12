[@@@warning "-26"]

open Core
open Z3
open Grammar

exception Unreachable

module ResKey = struct
  module T = struct
    type t = res [@@deriving compare, sexp, hash]
  end

  include T
  include Comparable.Make (T)
end

module AtomKey = struct
  module T = struct
    type t = atom [@@deriving compare, sexp, hash]
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
  Format.sprintf "P%d"
    (Hashtbl.find_or_add atom_to_id a ~default:(fun () ->
         incr fresh_id;
         !fresh_id))

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

let ( ==> ) vars body =
  Quantifier.expr_of_quantifier
    (Quantifier.mk_forall_const ctx vars body None [] [] None None)

let solver = Solver.mk_solver_s ctx "HORN"
let is_int_arith = function PlusOp _ | MinusOp _ -> true | _ -> false
let chcs = Hash_set.create (module E)

let find_or_add pid sort =
  match Hashtbl.find id_to_decl pid with
  | Some p -> p
  | None ->
      let p = zdecl pid [ sort ] bsort in
      Hashtbl.add_exn id_to_decl ~key:pid ~data:p;
      p

let reset () =
  Hashtbl.clear res_to_id;
  Hashtbl.clear id_to_decl;
  Hash_set.clear chcs;
  Solver.reset solver;
  fresh_id := -1

let rec cond pis =
  if List.is_empty pis then ([], ztrue)
  else (
    List.iter pis ~f:(fun (r, _) -> chcs_of_res r r ~pis:[]);
    let conjs =
      List.foldi pis
        ~f:(fun i conjs (r, b) ->
          let rid = Format.sprintf "c%d" i in
          let const = zconst rid bsort in
          let p = zdecl (idr r) [ bsort ] bsort in
          p <-- [ const ] &&& (const === zbool b) &&& conjs)
        ~init:ztrue
    in
    (List.mapi pis ~f:(fun i _ -> zconst (Format.sprintf "c%d" i) bsort), conjs))

and chcs_of_atom a r pis =
  match a with
  | IntAtom i ->
      let cond_quants, cond_body = cond pis in
      (*! different from written spec *)
      let p = find_or_add (ida a) isort in
      let body = p <-- [ zint i ] in
      Format.printf "reached me: %b\n" (List.is_empty pis);
      Hash_set.add chcs
        (if List.is_empty pis then body else cond_quants ==> cond_body --> body)
  | BoolAtom b ->
      let cond_quants, cond_body = cond pis in
      let p = find_or_add (idr r) bsort in
      let body = p <-- [ zbool b ] in
      Hash_set.add chcs
        (if List.is_empty pis then body else cond_quants ==> cond_body --> body)
  | OpAtom op -> (
      match op with
      | PlusOp (r1, r2)
      | MinusOp (r1, r2)
      | EqualOp (r1, r2)
      | AndOp (r1, r2)
      | OrOp (r1, r2) ->
          let pid, id1, id2 = (idr r, idr r1, idr r2) in
          let is_int_arith = is_int_arith op in
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
          ignore
            ( Hashtbl.add id_to_decl ~key:pid ~data:p,
              Hashtbl.add id_to_decl ~key:id1 ~data:p1,
              Hashtbl.add id_to_decl ~key:id2 ~data:p2 );
          let cond_quants, cond_body = cond pis in
          chcs_of_res r1 r1 ~pis;
          chcs_of_res r2 r2 ~pis;
          (* TODO: consider eliding cond_body if it's just `true` *)
          Hash_set.add chcs
            (const1 :: const2 :: cond_quants
            ==> (p1 <-- [ const1 ] &&& (p2 <-- [ const2 ]) &&& cond_body)
                --> (p <-- [ zop const1 const2 ]))
      | NotOp r' ->
          let pid, rid = (idr r, idr r') in
          let p = zdecl pid [ bsort ] bsort in
          let p' = zdecl rid [ bsort ] bsort in
          let const = zconst "r" bsort in
          ignore
            ( Hashtbl.add id_to_decl ~key:pid ~data:p,
              Hashtbl.add id_to_decl ~key:rid ~data:p' );
          let cond_quants, cond_body = cond pis in
          chcs_of_res r' r' ~pis;
          Hash_set.add chcs
            ((const :: cond_quants ==> (p' <-- [ const ]) &&& cond_body)
            --> (p <-- [ znot const ])))
  | LabelResAtom (r', _) | ExprResAtom (r', _) ->
      (* chcs_of_res r' ~pis *)
      List.iter r' ~f:(fun a ->
          (* TODO:  *)
          chcs_of_atom a r' pis;
          let pid, aid = (idr r', ida a) in
          (* Format.printf "looking up: %s\n" pid; *)
          (*! different from written spec *)
          match Hashtbl.find id_to_decl aid with
          | Some pa ->
              let adom = FuncDecl.get_domain pa in
              let p = zdecl pid adom bsort in
              ignore @@ Hashtbl.add id_to_decl ~key:pid ~data:p;
              (* TODO: start here *)
              let consta = zconst "r" (List.hd_exn adom) in
              let cond_quants, cond_body = cond pis in
              Hash_set.add chcs
                ((consta :: cond_quants ==> (pa <-- [ consta ] &&& cond_body))
                --> (p <-- [ consta ]))
          | None ->
              Format.printf "%a\n" Utils.pp_res r';
              Format.printf "%a\n" Utils.pp_atom a;
              failwith "resatom")
  | PathCondAtom (pi, r') -> chcs_of_res r' r ~pis:(pi :: pis)
  | FunAtom _ | LabelStubAtom _ | ExprStubAtom _ -> ()
  | RecordAtom _ -> failwith "unimplemented"
  | ProjectionAtom _ -> failwith "unimplemented"
  | InspectionAtom _ -> failwith "unimplemented"

and chcs_of_res ?(pis = []) r p =
  (* TODO: still need to make an atom constructor for unlabeled res
     to realize toCHC spec *)
  List.iter r ~f:(fun a -> chcs_of_atom a p pis)

(* entry point *)
let chcs_of_res r = chcs_of_res r r
