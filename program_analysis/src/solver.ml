open Core
open Z3
open Grammar
open Utils

exception Unreachable
exception BadAssert

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
let ( *** ) e1 e2 = Arithmetic.mk_mul ctx [ e1; e2 ]
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
let chcs_of_assert r1 (r2 : Interpreter.Ast.result_value_fv) =
  let p = Hashtbl.find_exn id_to_decl (idr r1) in
  let ri = zconst "r" isort in
  let rb = zconst "r" bsort in
  match r2 with
  | BoolResultFv b -> Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> zbool b)
  | VarResultFv id' ->
      Hash_set.add chcs ([ rb ] |. (p <-- [ rb ]) --> rb === ztrue)
  | OpResultFv op -> (
      match op with
      | EqOpFv (v1, IntResultFv i)
      | GeOpFv (v1, IntResultFv i)
      | GtOpFv (v1, IntResultFv i)
      | LeOpFv (v1, IntResultFv i)
      | LtOpFv (v1, IntResultFv i) -> (
          let op =
            match op with
            | EqOpFv _ -> ( === )
            | GeOpFv _ -> ( >== )
            | GtOpFv _ -> ( >>> )
            | LeOpFv _ -> ( <== )
            | LtOpFv _ -> ( <<< )
            | _ -> raise Unreachable
          in
          (* LHS of assertion *)
          match v1 with
          | VarResultFv _ ->
              Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> op ri (zint i))
          | ProjectionResultFv (VarResultFv _, Ident x) ->
              let p =
                let r1_hd = List.hd_exn r1 in
                match r1_hd with
                | RecordAtom _ ->
                    Hashtbl.find_exn id_to_decl (ida r1_hd ^ "_" ^ x)
                | LabelResAtom ([ a ], _) ->
                    Hashtbl.find_exn id_to_decl (ida a ^ "_" ^ x)
                | _ ->
                    (* Format.printf "%a\n" Grammar.pp_atom r1_hd; *)
                    raise Unreachable
              in
              Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> op ri (zint i))
          | _ -> raise Unreachable)
      | NotOpFv _ ->
          Hash_set.add chcs ([ rb ] |. (p <-- [ rb ]) --> (rb === zfalse))
      | _ -> raise Unreachable)
  | _ -> raise BadAssert

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
      | MultOp (r1, r2)
      | EqualOp (r1, r2)
      | AndOp (r1, r2)
      | OrOp (r1, r2)
      | GeOp (r1, r2)
      | GtOp (r1, r2)
      | LeOp (r1, r2)
      | LtOp (r1, r2) ->
          let aid, rid1, rid2 = (ida a, idr r1, idr r2) in
          let is_int_arith =
            match op with PlusOp _ | MinusOp _ | MultOp _ -> true | _ -> false
          in
          let zop =
            match op with
            | PlusOp _ -> ( +++ )
            | MinusOp _ -> ( --- )
            | MultOp _ -> ( *** )
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
            | PlusOp _ | MinusOp _ | MultOp _ | EqualOp _ | GeOp _ | GtOp _
            | LeOp _ | LtOp _ ->
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
  | PathCondAtom (((r, _) as pi), r0) ->
      (* generate CHCs for current path condition using
         the previous path conditions *)
      chcs_of_res r ~pis;
      chcs_of_res r0 ~pis:(pi :: pis);
      (* point self at the same decl *)
      ignore
        (Hashtbl.add id_to_decl ~key:(ida a)
           ~data:(Hashtbl.find_exn id_to_decl (idr r0)))
  | FunAtom _ | LabelStubAtom _ | ExprStubAtom _ -> ()
  | RecordAtom entries ->
      let aid = ida a in
      (* Format.printf "aid: %s\nrecord: %a\n" aid Grammar.pp_atom a; *)
      let pa = zdecl aid [ isort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      List.iter entries ~f:(fun (Ident x, r) ->
          chcs_of_res r ~pis;
          let pr = Hashtbl.find_exn id_to_decl (idr r) in
          (* Format.printf "%s -> %s\n" (aid ^ "_" ^ x) (idr r);
             Format.printf "%a\n" Grammar.pp_res r; *)
          ignore (Hashtbl.add id_to_decl ~key:(aid ^ "_" ^ x) ~data:pr);
          let r_ = zconst "r" isort in
          Hash_set.add chcs ([ r_ ] |. (pr <-- [ r_ ]) --> (pa <-- [ r_ ])))
  | ProjectionAtom (r, Ident x) ->
      Format.printf "projectionatom:\n%a\n" Utils.pp_res r;
      (* Format.printf "__________\n%a\n" Grammar.pp_res r; *)
      chcs_of_res r ~pis
      (* let record = List.hd_exn r in *)
      (* ignore
         (Hashtbl.add id_to_decl ~key:(ida a)
            ~data:(Hashtbl.find_exn id_to_decl (ida record ^ "_" ^ x))) *)
  | InspectionAtom _ -> failwith "inspection"
  (* records are good for: subsumes shape analysis *)
  | AssertAtom (id, r1, r2) ->
      chcs_of_res r1 ~pis;
      chcs_of_assert r1 r2

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
          (* Format.printf "%a\n" Grammar.pp_atom a; *)
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

let verify_result r =
  (* let solver = Z3.Solver.mk_solver_s ctx "HORN" in *)
  chcs_of_res r;
  let chcs = list_of_chcs () in
  Z3.Solver.add solver chcs;

  (* let start = Stdlib.Sys.time () in *)
  let status = Z3.Solver.check solver [] in

  (* Format.printf "verification time: %f\n" (Stdlib.Sys.time () -. start); *)
  (* List.iter chcs ~f:(fun chc -> Format.printf "%s\n" (Z3.Expr.to_string chc)); *)
  match status with
  | SATISFIABLE ->
      (* Format.printf "sat" *)
      (* let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
         model |> Z3.Model.to_string |> pf "Model:\n%s\n\n"; *)
      (* solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s"; *)
      reset ()
  | UNSATISFIABLE ->
      reset ();
      failwith "unsat"
  | UNKNOWN ->
      reset ();
      failwith "unknown"
