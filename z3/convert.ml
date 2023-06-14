open Core
open Z3
open Program_analysis.Grammar

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
  Format.sprintf "%d"
    (Hashtbl.find_or_add res_to_id r ~default:(fun () ->
         incr fresh_id;
         !fresh_id))

module CHCSet = Core.Set.Make (E)

let id_to_decl = Hashtbl.create (module String)
let id_to_expr = Hashtbl.create (module String)
let ctx = mk_context [ ("proof", "true") ]
let int_sort = Arithmetic.Integer.mk_sort ctx
let bool_sort = Boolean.mk_sort ctx
let zi i = Arithmetic.Integer.mk_numeral_i ctx i
let ztrue = Boolean.mk_true ctx
let zfalse = Boolean.mk_false ctx
let zconst s sort = Expr.mk_const_s ctx s sort
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

(* let solver = Solver.mk_solver_s ctx "HORN" *)

let reset solver =
  Hashtbl.clear res_to_id;
  Hashtbl.clear id_to_decl;
  Solver.reset solver;
  fresh_id := -1

let rec chcs_of_res r =
  List.fold r ~init:(CHCSet.empty, []) ~f:(fun (assns, negs) -> function
    | IntAtom i -> (
        let i_expr = zi i in
        let _id = id r in
        match Hashtbl.find id_to_decl _id with
        | Some p -> (CHCSet.add assns (p <-- [ i_expr ]), [])
        | None ->
            let p =
              FuncDecl.mk_func_decl_s ctx ("P" ^ _id) [ int_sort ] bool_sort
            in
            Hashtbl.add_exn id_to_decl ~key:_id ~data:p;
            (CHCSet.add assns (p <-- [ i_expr ]), []))
    | BoolAtom b -> (
        let b_expr = Boolean.mk_val ctx b in
        let _id = id r in
        match Hashtbl.find id_to_decl _id with
        | Some p -> (CHCSet.add assns (p <-- [ b_expr ]), [])
        | None ->
            let p =
              FuncDecl.mk_func_decl_s ctx ("P" ^ _id) [ bool_sort ] bool_sort
            in
            Hashtbl.add_exn id_to_decl ~key:_id ~data:p;
            ( CHCSet.add assns (p <-- [ b_expr ]),
              [ (p <-- [ ztrue ]) --> zfalse; (p <-- [ zfalse ]) --> zfalse ] ))
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | EqualOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            let _id, id1, id2 = (id r, id r1, id r2) in
            let rid1, rid2 = ("r" ^ id1, "r" ^ id2) in
            let pid, pid1, pid2 = ("P" ^ _id, "P" ^ id1, "P" ^ id2) in
            let r1_const, r2_const =
              ( Expr.mk_const_s ctx rid1
                  (match op with
                  | PlusOp _ | MinusOp _ | EqualOp _ -> int_sort
                  | _ -> bool_sort),
                Expr.mk_const_s ctx rid2
                  (match op with
                  | PlusOp _ | MinusOp _ | EqualOp _ -> int_sort
                  | _ -> bool_sort) )
            in
            let p, p1, p2 =
              ( FuncDecl.mk_func_decl_s ctx pid
                  [
                    (match op with
                    | PlusOp _ | MinusOp _ -> int_sort
                    | _ -> bool_sort);
                  ]
                  bool_sort,
                FuncDecl.mk_func_decl_s ctx pid1
                  [
                    (match op with
                    | PlusOp _ | MinusOp _ | EqualOp _ -> int_sort
                    | _ -> bool_sort);
                  ]
                  bool_sort,
                FuncDecl.mk_func_decl_s ctx pid2
                  [
                    (match op with
                    | PlusOp _ | MinusOp _ | EqualOp _ -> int_sort
                    | _ -> bool_sort);
                  ]
                  bool_sort )
            in
            ignore
              ( Hashtbl.add id_to_expr ~key:rid1 ~data:r1_const,
                Hashtbl.add id_to_expr ~key:rid2 ~data:r2_const,
                Hashtbl.add id_to_decl ~key:_id ~data:p,
                Hashtbl.add id_to_decl ~key:id1 ~data:p1,
                Hashtbl.add id_to_decl ~key:id2 ~data:p2 );
            ( CHCSet.add
                (CHCSet.union_list
                   [ assns; fst @@ chcs_of_res r1; fst @@ chcs_of_res r2 ])
                ([ r1_const; r2_const ]
                ==> (p1 <-- [ r1_const ] &&& (p2 <-- [ r2_const ]))
                    --> (p
                        <-- [
                              (match op with
                              | PlusOp _ -> r1_const +++ r2_const
                              | MinusOp _ -> r1_const --- r2_const
                              | EqualOp _ -> r1_const === r2_const
                              | AndOp _ -> r1_const &&& r2_const
                              | OrOp _ -> r1_const ||| r2_const
                              | _ -> raise Unreachable);
                            ])),
              [ (p <-- [ ztrue ]) --> zfalse; (p <-- [ zfalse ]) --> zfalse ] )
        | _ -> failwith "not implemented")
    | FunAtom _ -> failwith "funatom"
    | LabelResAtom (r', _) | ExprResAtom (r', _) ->
        List.fold r' ~init:(assns, negs) ~f:(fun (assns, negs) a ->
            let chcs, _ = chcs_of_res [ a ] in
            let ida = id [ a ] in
            let _id = id r in
            match Hashtbl.find id_to_decl _id with
            | Some p ->
                let p_domain = FuncDecl.get_domain p in
                let pa =
                  FuncDecl.mk_func_decl_s ctx ("P" ^ ida) p_domain bool_sort
                in
                ignore @@ Hashtbl.add id_to_decl ~key:ida ~data:pa;
                let a_const = zconst "r" (List.hd_exn p_domain) in
                ( CHCSet.add (CHCSet.union assns chcs)
                    ([ a_const ]
                    ==> (pa <-- [ a_const ]) --> (p <-- [ a_const ])),
                  negs )
            | None -> failwith "yo")
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
