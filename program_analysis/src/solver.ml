[@@@warning "-26"]

open Core
open Z3
open Grammar

exception Unreachable

module R = struct
  module T = struct
    type t = res [@@deriving compare, sexp, hash]
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

let res_to_id = Hashtbl.create (module R)
let fresh_id = ref (-1)

let id r =
  Format.sprintf "P%d"
    (Hashtbl.find_or_add res_to_id r ~default:(fun () ->
         incr fresh_id;
         !fresh_id))

module CHCSet = Core.Set.Make (E)

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

let reset () =
  Hashtbl.clear res_to_id;
  Hashtbl.clear id_to_decl;
  Solver.reset solver;
  fresh_id := -1

let cond pis =
  if List.is_empty pis then ztrue
  else
    let conjs =
      List.foldi pis
        ~f:
          (fun i conjs -> function
            | r, b -> (
                let rid = Format.sprintf "r%d" i in
                let const = zconst rid bsort in
                let pid = id r in
                match Hashtbl.find id_to_decl pid with
                | Some p ->
                    (* let p = zdecl pid [ bsort ] bsort in *)
                    p <-- [ const ] === zbool b &&& conjs
                | None -> failwith "TODO: ISSUE HERE"))
        ~init:ztrue
    in
    List.mapi pis ~f:(fun i _ -> zconst (Format.sprintf "r%d" i) bsort)
    ==> conjs

let is_int_arith = function PlusOp _ | MinusOp _ -> true | _ -> false

let rec chcs_of_res r real_r pis =
  (* TODO: still need to make an atom constructor for unlabeled res
     to realize toCHC spec *)
  List.fold r ~init:CHCSet.empty ~f:(fun assns -> function
    | IntAtom i -> (
        let pid = id r in
        match Hashtbl.find id_to_decl pid with
        | Some p -> CHCSet.add assns (cond pis --> (p <-- [ zint i ]))
        | None ->
            let p = zdecl pid [ isort ] bsort in
            Hashtbl.add_exn id_to_decl ~key:pid ~data:p;
            CHCSet.add assns (cond pis --> (p <-- [ zint i ])))
    | BoolAtom b -> (
        let pid = id r in
        match Hashtbl.find id_to_decl pid with
        | Some p -> CHCSet.add assns (cond pis --> (p <-- [ zbool b ]))
        | None ->
            let p = zdecl pid [ bsort ] bsort in
            Hashtbl.add_exn id_to_decl ~key:pid ~data:p;
            CHCSet.add assns (cond pis --> (p <-- [ zbool b ])))
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | EqualOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            let pid, id1, id2 = (id r, id r1, id r2) in
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
            let p =
              zdecl pid [ (if is_int_arith then isort else bsort) ] bsort
            in
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
            CHCSet.add
              (CHCSet.union_list
                 [ assns; chcs_of_res r1 r1 pis; chcs_of_res r2 r2 pis ])
              ([ const1; const2 ]
              ==> (p1 <-- [ const1 ] &&& (p2 <-- [ const2 ]) &&& cond pis)
                  --> (p <-- [ zop const1 const2 ]))
        | NotOp _ -> failwith "not implemented")
    | LabelResAtom (r', _) | ExprResAtom (r', _) ->
        let conjs =
          List.fold r' ~init:CHCSet.empty ~f:(fun assns a ->
              let chcs = chcs_of_res [ a ] r' pis in
              let pid, aid = (id r', id [ a ]) in
              match Hashtbl.find id_to_decl pid with
              | Some p ->
                  let pdom = FuncDecl.get_domain p in
                  let pa = zdecl aid pdom bsort in
                  ignore @@ Hashtbl.add id_to_decl ~key:aid ~data:pa;
                  let consta = zconst "r" (List.hd_exn pdom) in
                  CHCSet.add (CHCSet.union assns chcs)
                    (([ consta ] ==> (pa <-- [ consta ]) &&& cond pis)
                    --> (p <-- [ consta ]))
              | None -> failwith "resatom")
        in
        List.fold r' ~init:conjs ~f:(fun assns a ->
            CHCSet.union assns (chcs_of_res [ a ] r' pis))
    | FunAtom _ | LabelStubAtom _ | ExprStubAtom _ -> assns
    | PathCondAtom (pi, a) -> chcs_of_res a a (pi :: pis)
    | RecordAtom _ -> failwith "unimplemented"
    | ProjectionAtom _ -> failwith "unimplemented"
    | InspectionAtom _ -> failwith "unimplemented")
