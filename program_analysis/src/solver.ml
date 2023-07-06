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

(* module Test = struct
     module T = struct
       type t = int list [@@deriving compare, sexp, hash]
     end

     include T
     include Comparable.Make (T)
   end

   let test_tbl = Hashtbl.create (module Test)

   let ttt _ =
     Hashtbl.add_exn test_tbl ~key:[ 1; 2; 3 ] ~data:"hello";
     Format.printf "%s"
       (Hashtbl.find_or_add test_tbl [ 1; 2; 3 ] ~default:(fun () -> "yo")) *)

module E = struct
  module T = struct
    type t = Expr.expr

    let compare = Expr.compare
    let sexp_of_t e = e |> Expr.ast_of_expr |> AST.to_sexpr |> Sexp.of_string
    let t_of_sexp s = failwith "yo"
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
let int_sort = Arithmetic.Integer.mk_sort ctx
let bool_sort = Boolean.mk_sort ctx
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

let is_int_arith = function PlusOp _ | MinusOp _ -> true | _ -> false

let rec has_stub r =
  List.exists r ~f:(function
    | LabelStubAtom _ | ExprStubAtom _ -> true
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | EqualOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            has_stub r1 || has_stub r2
        | NotOp r -> has_stub r)
    | LabelResAtom (r, _) | ExprResAtom (r, _) -> has_stub r
    | _ -> false)

let rec chcs_of_res r =
  (* TODO: should probably add a constructor to atom for untagged Res *)
  List.fold r ~init:(CHCSet.empty, []) ~f:(fun (assns, negs) -> function
    | IntAtom i -> (
        let _id = id r in
        match Hashtbl.find id_to_decl _id with
        | Some p -> (CHCSet.add assns (p <-- [ zint i ]), [])
        | None ->
            let p = zdecl _id [ int_sort ] bool_sort in
            Hashtbl.add_exn id_to_decl ~key:_id ~data:p;
            (CHCSet.add assns (p <-- [ zint i ]), []))
    | BoolAtom b -> (
        let _id = id r in
        match Hashtbl.find id_to_decl _id with
        | Some p -> (CHCSet.add assns (p <-- [ zbool b ]), [])
        | None ->
            let p = zdecl _id [ bool_sort ] bool_sort in
            Hashtbl.add_exn id_to_decl ~key:_id ~data:p;
            ( CHCSet.add assns (p <-- [ zbool b ]),
              [ (p <-- [ ztrue ]) --> zfalse; (p <-- [ zfalse ]) --> zfalse ] ))
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | EqualOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            let _id, id1, id2 = (id r, id r1, id r2) in
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
            if has_stub r then (
              (* encoding scheme for cyclic programs *)
              let idn = _id ^ "n" in
              let gen_p id =
                zdecl id
                  (match op with
                  | PlusOp _ | MinusOp _ -> [ int_sort; int_sort; int_sort ]
                  | EqualOp _ -> [ int_sort; int_sort; bool_sort ]
                  | _ -> [ bool_sort; bool_sort; bool_sort ])
                  bool_sort
              in
              let p =
                if is_int_arith then zdecl _id [ int_sort ] bool_sort
                else gen_p _id
              in
              let pn = gen_p idn in
              let sort =
                if is_int_arith then int_sort
                else List.hd_exn (FuncDecl.get_domain p)
              in
              let p1, p2 =
                (zdecl id1 [ sort ] bool_sort, zdecl id2 [ sort ] bool_sort)
              in
              let const1, const2 = (zconst "r1" sort, zconst "r2" sort) in
              ignore
                ( Hashtbl.add id_to_decl ~key:_id ~data:p,
                  Hashtbl.add id_to_decl ~key:idn ~data:pn,
                  Hashtbl.add id_to_decl ~key:id1 ~data:p1,
                  Hashtbl.add id_to_decl ~key:id2 ~data:p2 );
              let zope = zop const1 const2 in
              let gen_p_assn is_pn =
                [ const1; const2 ]
                ==> (p1 <-- [ const1 ] &&& (p2 <-- [ const2 ]))
                    --> ((if is_pn then pn else p)
                        <-- [
                              const1;
                              const2;
                              (if is_pn then znot zope else zope);
                            ])
              in
              let main_assns =
                CHCSet.union_list
                  [
                    assns;
                    fst @@ chcs_of_res r1;
                    fst @@ chcs_of_res r2;
                    CHCSet.of_list
                      (if is_int_arith then
                         [
                           [ const1; const2 ]
                           ==> (p1 <-- [ const1 ] &&& (p2 <-- [ const2 ]))
                               --> (p <-- [ zope ]);
                         ]
                       else [ gen_p_assn false; gen_p_assn true ]);
                  ]
              in
              ( main_assns,
                if is_int_arith then
                  [
                    (p <-- [ ztrue ]) --> zfalse; (p <-- [ zfalse ]) --> zfalse;
                  ]
                else
                  [
                    [ const1; const2 ]
                    ==> (p <-- [ const1; const2; znot zope ]) --> zfalse;
                    [ const1; const2 ]
                    ==> (pn <-- [ const1; const2; zope ]) --> zfalse;
                  ] ))
            else
              (* encoding scheme for non-cyclic programs *)
              let p =
                zdecl _id
                  [ (if is_int_arith then int_sort else bool_sort) ]
                  bool_sort
              in
              let sort =
                match op with
                | PlusOp _ | MinusOp _ | EqualOp _ -> int_sort
                | _ -> bool_sort
              in
              let p1, p2 =
                (zdecl id1 [ sort ] bool_sort, zdecl id2 [ sort ] bool_sort)
              in
              let const1, const2 = (zconst "r1" sort, zconst "r2" sort) in
              ignore
                ( Hashtbl.add id_to_decl ~key:_id ~data:p,
                  Hashtbl.add id_to_decl ~key:id1 ~data:p1,
                  Hashtbl.add id_to_decl ~key:id2 ~data:p2 );
              ( CHCSet.add
                  (CHCSet.union_list
                     [ assns; fst @@ chcs_of_res r1; fst @@ chcs_of_res r2 ])
                  ([ const1; const2 ]
                  ==> (p1 <-- [ const1 ] &&& (p2 <-- [ const2 ]))
                      --> (p <-- [ zop const1 const2 ])),
                [ (p <-- [ ztrue ]) --> zfalse; (p <-- [ zfalse ]) --> zfalse ]
              )
        | NotOp _ -> failwith "not implemented")
    | FunAtom _ -> (assns, negs)
    | LabelResAtom (r', _) | ExprResAtom (r', _) ->
        List.fold r' ~init:(assns, negs) ~f:(fun (assns, negs) a ->
            let chcs, _ = chcs_of_res [ a ] in
            let _id, ida = (id r, id [ a ]) in
            match Hashtbl.find id_to_decl _id with
            | Some p ->
                let p_domain = FuncDecl.get_domain p in
                let pa = zdecl ida p_domain bool_sort in
                ignore @@ Hashtbl.add id_to_decl ~key:ida ~data:pa;
                let a_const = zconst "r" (List.hd_exn p_domain) in
                ( CHCSet.add (CHCSet.union assns chcs)
                    ([ a_const ]
                    ==> (pa <-- [ a_const ]) --> (p <-- [ a_const ])),
                  negs )
            | None -> failwith "resatom")
    | LabelStubAtom _ -> (assns, negs)
    | ExprStubAtom _ -> (assns, negs)
    | PathCondAtom _ -> failwith "pathcondatom"
    | RecordAtom _ -> failwith "recordatom"
    | ProjectionAtom _ -> failwith "projectionatom"
    | InspectionAtom _ -> failwith "inspectionatom")

let test1 _ = chcs_of_res [ IntAtom 100 ]
let test2 _ = chcs_of_res [ BoolAtom false ]
let test3 _ = chcs_of_res [ OpAtom (PlusOp ([ IntAtom 1 ], [ IntAtom 2 ])) ]

let test4 _ =
  chcs_of_res
    [
      OpAtom
        (PlusOp
           ([ OpAtom (PlusOp ([ IntAtom 1 ], [ IntAtom 2 ])) ], [ IntAtom 3 ]));
    ]

let test5 _ = chcs_of_res [ OpAtom (EqualOp ([ IntAtom 1 ], [ IntAtom 2 ])) ]

let test6 _ =
  chcs_of_res [ OpAtom (EqualOp ([ LabelStubAtom (1, []) ], [ IntAtom 2 ])) ]

let test7 _ =
  chcs_of_res
    [
      OpAtom
        (EqualOp
           ( [
               LabelResAtom
                 ( [
                     IntAtom 10;
                     OpAtom
                       (MinusOp ([ LabelStubAtom (-1, []) ], [ IntAtom 1 ]));
                   ],
                   (-1, []) );
             ],
             [ IntAtom 0 ] ));
    ]

(* TODOs:
   - write our own solver with crude heuristics
   - compare against forward analysis *)
