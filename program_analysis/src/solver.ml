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
    | LResAtom (_, st) -> (
        match Hashtbl.find atom_to_id (LStubAtom st) with
        | Some id -> Some id
        (* if a stub is not found, then `a` is not involved
           in any cycle *)
        | None -> Hashtbl.find atom_to_id a)
    | EResAtom (_, st) -> (
        match Hashtbl.find atom_to_id (EStubAtom st) with
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
let chcs = Hash_set.create (module Z3ExprKey)
let list_of_chcs () = Hash_set.to_list chcs
let entry_decl = ref None

let find_or_add aid sort =
  match Hashtbl.find id_to_decl aid with
  (* TODO: does the same leaf atom need to be assigned different predicates? *)
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
let chcs_of_assert r1 (r2 : Interp.Ast.res_val_fv) =
  let p = Hashtbl.find_exn id_to_decl (idr r1) in
  let ri = zconst "r" isort in
  let rb = zconst "r" bsort in
  match r2 with
  | BoolResFv b -> Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> zbool b)
  | VarResFv id' -> Hash_set.add chcs ([ rb ] |. (p <-- [ rb ]) --> rb === ztrue)
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
      | VarResFv _ ->
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> op ri (zint i))
      | ProjResFv (VarResFv _, Ident x) ->
          let p =
            let r1_hd = List.hd_exn r1 in
            match r1_hd with
            | RecAtom _ -> Hashtbl.find_exn id_to_decl (ida r1_hd ^ "_" ^ x)
            | LResAtom ([ a ], _) ->
                Hashtbl.find_exn id_to_decl (ida a ^ "_" ^ x)
            | _ -> raise Unreachable
          in
          Hash_set.add chcs ([ ri ] |. (p <-- [ ri ]) --> op ri (zint i))
      | _ -> raise Unreachable)
  | NotResFv _ ->
      Hash_set.add chcs ([ rb ] |. (p <-- [ rb ]) --> (rb === zfalse))
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

and chcs_of_atom ?(pis = []) ?(stub_sort = isort)
    ?(p = Core.Set.empty (module St)) a =
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
      let aid, rid1, rid2 = (ida a, idr r1, idr r2) in
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
        (zdecl rid1 [ param_sort ] bsort, zdecl rid2 [ param_sort ] bsort)
      in
      let r1_, r2_ = (zconst "r1" param_sort, zconst "r2" param_sort) in
      ignore
        ( Hashtbl.add id_to_decl ~key:aid ~data:pa,
          Hashtbl.add id_to_decl ~key:rid1 ~data:pr1,
          Hashtbl.add id_to_decl ~key:rid2 ~data:pr2 );
      let cond_quants, cond_body = cond pis in
      chcs_of_res r1 ~pis ~stub_sort:param_sort ~p;
      chcs_of_res r2 ~pis ~stub_sort:param_sort ~p;
      Hash_set.add chcs
        (r1_ :: r2_ :: cond_quants
        |. (pr1 <-- [ r1_ ] &&& (pr2 <-- [ r2_ ]) &&& cond_body)
           --> (pa <-- [ zop r1_ r2_ ]))
  | NotAtom r ->
      let aid, rid = (ida a, idr r) in
      let pa = zdecl aid [ bsort ] bsort in
      let pr = zdecl rid [ bsort ] bsort in
      let r_ = zconst "r" bsort in
      ignore
        ( Hashtbl.add id_to_decl ~key:aid ~data:pa,
          Hashtbl.add id_to_decl ~key:rid ~data:pr );
      let cond_quants, cond_body = cond pis in
      chcs_of_res r ~pis ~stub_sort:bsort ~p;
      Hash_set.add chcs
        ((r_ :: cond_quants |. (pr <-- [ r_ ]) &&& cond_body)
        --> (pa <-- [ znot r_ ]))
  | LResAtom (r, st) ->
      (* derive Z3 sort for labeled result/stub pair from the sort of
         the concrete disjuncts, which is sound on any proper,
         terminating programs. *)
      let p = Core.Set.add p (St.Lstate st) in
      let sort =
        List.fold r ~init:None ~f:(fun t a ->
            (* this may assign an ID for stub to be later inherited by
               its enclosing res atom but will trigger a lookup failure
               (caught) at stub's (non-existent) Z3 decl *)
            chcs_of_atom a ~pis ~stub_sort ~p;
            match Hashtbl.find id_to_decl (ida a) with
            | Some pa ->
                (* TODO: assert that all disjuncts are of the same type *)
                Some (pa |> FuncDecl.get_domain |> List.hd_exn)
            | None -> t (* should hit this case at least once *))
        |> function
        | Some t -> t
        | None ->
            Format.printf "%a\n" Grammar.pp_res r;
            raise Unreachable
      in
      let aid = ida a in
      let pa = zdecl aid [ sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      let rid = idr r in
      let pr = zdecl rid [ sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:rid ~data:pr);
      (* most of this is repetitive work, but necessary *)
      chcs_of_res r ~pis ~stub_sort ~p;
      let r_ = zconst "r" sort in
      Hash_set.add chcs ([ r_ ] |. (pr <-- [ r_ ]) --> (pa <-- [ r_ ]))
  | EResAtom (r, st) ->
      let p = Core.Set.add p (St.Estate st) in
      let sort =
        List.fold r ~init:None ~f:(fun t a ->
            chcs_of_atom a ~pis ~stub_sort ~p;
            match Hashtbl.find id_to_decl (ida a) with
            | Some pa ->
                (* TODO: assert that all disjuncts are of the same type *)
                Some (pa |> FuncDecl.get_domain |> List.hd_exn)
            | None -> t)
        |> function
        | Some t -> t
        | None ->
            Format.printf "%a\n" Grammar.pp_res r;
            raise Unreachable
      in
      let aid = ida a in
      let pa = zdecl aid [ sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      let rid = idr r in
      let pr = zdecl rid [ sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:rid ~data:pr);
      chcs_of_res r ~pis ~stub_sort ~p;
      let r_ = zconst "r" sort in
      Hash_set.add chcs ([ r_ ] |. (pr <-- [ r_ ]) --> (pa <-- [ r_ ]))
  | PathCondAtom (((r, _) as pi), r0) -> (
      (* generate CHCs for current path condition using
         the previous path conditions *)
      chcs_of_res r ~pis ~stub_sort ~p;
      chcs_of_res r0 ~pis:(pi :: pis) ~stub_sort ~p;
      (* chcs_of_res r0 ~pis ~stub_sort; *)
      (* point self at the same decl *)
      match Hashtbl.find id_to_decl (idr r0) with
      | Some decl -> ignore (Hashtbl.add id_to_decl ~key:(ida a) ~data:decl)
      | None -> ())
  | FunAtom _ -> ()
  | LStubAtom ((l, s) as st) ->
      let aid = ida a in
      let pa = zdecl aid [ stub_sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      if not (Core.Set.mem p (St.Lstate st)) then
        (* Format.printf "lstub: %s\n" aid; *)
        let r_ = zconst "r" stub_sort in
        Hash_set.add chcs ([ r_ ] |. (pa <-- [ r_ ]))
  | EStubAtom ((e, s) as st) ->
      let aid = ida a in
      let pa = zdecl aid [ stub_sort ] bsort in
      ignore (Hashtbl.add id_to_decl ~key:aid ~data:pa);
      if not (Core.Set.mem p (St.Estate st)) then
        (* Format.printf "estub: %s\n" aid; *)
        let r_ = zconst "r" stub_sort in
        Hash_set.add chcs ([ r_ ] |. (pa <-- [ r_ ]))
  | AssertAtom (id, r1, r2) ->
      chcs_of_res r1 ~pis ~stub_sort ~p;
      chcs_of_assert r1 r2
  (* records are good for: subsumes shape analysis *)
  | RecAtom _ -> ()
  | ProjAtom _ | InspAtom _ -> raise Unreachable

and chcs_of_res ?(pis = []) ?(stub_sort = isort)
    ?(p = Core.Set.empty (module St)) r =
  let rid = idr r in
  List.iter r ~f:(fun a ->
      chcs_of_atom a ~pis ~stub_sort ~p;
      let aid = ida a in
      let cond_quants, cond_body = cond pis in
      match Hashtbl.find id_to_decl aid with
      | Some pa ->
          let dom = FuncDecl.get_domain pa in
          let pr = zdecl rid dom bsort in
          (* at if conditions, the root assertion is always P0 *)
          if String.(rid = "P0") then entry_decl := Some pr;
          ignore (Hashtbl.add id_to_decl ~key:rid ~data:pr);
          let r = zconst "r" (List.hd_exn dom) in
          (* TODO: add flag to leave all path conditions out *)
          Hash_set.add chcs
            (r :: cond_quants |. (pa <-- [ r ] &&& cond_body) --> (pr <-- [ r ]))
      | None ->
          (* AssertAtom *)
          (* Format.printf "%a\n" Grammar.pp_atom a *)
          ())

let verify_result r =
  (* let solver = Z3.Solver.mk_solver_s ctx "HORN" in *)
  chcs_of_res r;
  (* Format.printf "atom_to_id\n";
     Hashtbl.iteri atom_to_id ~f:(fun ~key ~data ->
         Format.printf "%a -> %d\n" pp_atom key data);
     Format.printf "res_to_id\n";
     Hashtbl.iteri res_to_id ~f:(fun ~key ~data ->
         Format.printf "%a -> %d\n" pp_res key data); *)
  let chcs = list_of_chcs () in
  Z3.Solver.add solver chcs;

  (* let start = Stdlib.Sys.time () in *)
  let status = Z3.Solver.check solver [] in

  (* Format.printf "verification time: %f\n" (Stdlib.Sys.time () -. start); *)
  (* List.iter chcs ~f:(fun chc -> Format.printf "%s\n" (Z3.Expr.to_string chc)); *)
  (* solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s"; *)
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
