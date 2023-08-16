open Core
open Core.Option.Let_syntax
open Interpreter.Ast
open Grammar
open Utils
open Solver
open Logs

exception Unreachable
exception BadAssert
exception TypeMismatch

let empty_choice_set = Set.empty (module Choice)

(* controls whether to generate logs; log file is "logs" in _build directory *)
let gen_logs = ref false
let log msg = if !gen_logs then info (fun m -> m msg)
let info msg = if !gen_logs then info msg

(* maximum recursion depth ever reached by execution so far *)
let max_d = ref 0

let solve_cond r b =
  (* let solver = Z3.Solver.mk_solver_s ctx "HORN" in *)
  Solver.chcs_of_res r;
  let p = Option.value_exn !Solver.entry_decl in
  let chcs = Hash_set.to_list Solver.chcs in
  let rb = zconst "r" bsort in
  let manual = [ rb ] |. (p <-- [ rb ]) --> (rb === zbool b) in
  Z3.Solver.add solver (manual :: chcs);

  (* let start = Stdlib.Sys.time () in *)
  let status = Z3.Solver.check solver [] in
  (* Format.printf "cond execution time: %f\n" (Stdlib.Sys.time () -. start); *)
  let sat =
    match status with
    | SATISFIABLE ->
        (* let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
           model |> Z3.Model.to_string |> Format.printf "Model:\n%s\n\n"; *)
        (* Format.printf "sat\n"; *)
        (* solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s"; *)
        (* let prog = Format.asprintf "%a" pp_res r in
           Format.printf "if condition: %s\n" prog; *)
        true
    | UNSATISFIABLE -> false
    | UNKNOWN -> failwith "unknown"
  in
  (* let start = Stdlib.Sys.time () in *)
  Solver.reset ();
  (* Format.printf "reset execution time: %f\n" (Stdlib.Sys.time () -. start); *)
  (* Format.print_flush (); *)
  sat

let rec eval_assert_aux e =
  match e with
  | Int i -> IntResultFv i
  | Bool b -> BoolResultFv b
  | Plus (e1, e2)
  | Minus (e1, e2)
  | Equal (e1, e2)
  | Ge (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Lt (e1, e2) -> (
      match (eval_assert_aux e1, eval_assert_aux e2) with
      | IntResultFv i1, IntResultFv i2 -> (
          match e with
          | Plus _ -> IntResultFv (i1 + i2)
          | Minus _ -> IntResultFv (i1 - i2)
          | Equal _ -> BoolResultFv (i1 = i2)
          | Ge _ -> BoolResultFv (i1 >= i2)
          | Gt _ -> BoolResultFv (i1 > i2)
          | Le _ -> BoolResultFv (i1 <= i2)
          | Lt _ -> BoolResultFv (i1 < i2)
          | _ -> raise Unreachable)
      | _ -> raise Unreachable)
  | And (e1, e2) | Or (e1, e2) -> (
      match (eval_assert_aux e1, eval_assert_aux e2) with
      | BoolResultFv b1, BoolResultFv b2 -> (
          match e with
          | And _ -> BoolResultFv (b1 && b2)
          | Or _ -> BoolResultFv (b1 || b2)
          | _ -> raise Unreachable)
      | _ -> raise Unreachable)
  | Not e -> (
      match eval_assert_aux e with
      | BoolResultFv b -> BoolResultFv (not b)
      | _ -> raise Unreachable)
  | _ ->
      Format.printf "%a" Interpreter.Pp.pp_expr e;
      raise BadAssert

(** only allows the following forms:
    - arbitrary variable-free arithmetic
    - <var>
    - not <var>
    - <var> <op> <value> *)
let eval_assert e id =
  match e with
  | Bool b -> BoolResultFv b
  | Var (id', _) when Stdlib.(id = id') -> VarResultFv id'
  | Equal (e1, e2) | Ge (e1, e2) | Gt (e1, e2) | Le (e1, e2) | Lt (e1, e2) -> (
      match e1 with
      | Var (id', _) when Stdlib.(id = id') ->
          let v1 = VarResultFv id' in
          let v2 = eval_assert_aux e2 in
          OpResultFv
            (match e with
            | Equal _ -> EqOpFv (v1, v2)
            | Ge _ -> GeOpFv (v1, v2)
            | Gt _ -> GtOpFv (v1, v2)
            | Le _ -> LeOpFv (v1, v2)
            | Lt _ -> LtOpFv (v1, v2)
            | _ -> raise Unreachable)
      | Projection (e1, x) -> (
          match e1 with
          | Var (id', _) when Stdlib.(id = id') ->
              let v1 = ProjectionResultFv (VarResultFv id', x) in
              let v2 = eval_assert_aux e2 in
              OpResultFv
                (match e with
                | Equal _ -> EqOpFv (v1, v2)
                | Ge _ -> GeOpFv (v1, v2)
                | Gt _ -> GtOpFv (v1, v2)
                | Le _ -> LeOpFv (v1, v2)
                | Lt _ -> LtOpFv (v1, v2)
                | _ -> raise Unreachable)
          | _ -> ProjectionResultFv (eval_assert_aux e1, x))
      | _ -> (
          let v1, v2 = (eval_assert_aux e1, eval_assert_aux e2) in
          match (v1, v2) with
          | IntResultFv i1, IntResultFv i2 -> (
              match e with
              | Equal _ -> BoolResultFv (i1 = i2)
              | Ge _ -> BoolResultFv (i1 >= i2)
              | Gt _ -> BoolResultFv (i1 > i2)
              | Le _ -> BoolResultFv (i1 <= i2)
              | Lt _ -> BoolResultFv (i1 < i2)
              | _ -> raise Unreachable)
          | _ -> raise BadAssert))
  (* TODO: support And/Or (low priority) *)
  | Not e' -> (
      match e' with
      | Var (id', _) when Stdlib.(id = id') ->
          OpResultFv (NotOpFv (VarResultFv id'))
      | _ -> eval_assert_aux e')
  | _ -> raise BadAssert

exception Bad_type

let rec eval_int ~m ~cnt r =
  List.fold r
    ~init:(Set.empty (module Maybe_prim))
    ~f:(fun acc a ->
      match a with
      | BoolAtom _ | FunAtom _ | RecordAtom _ | InspectionAtom _ ->
          raise Bad_type
      | IntAtom i -> Set.add acc (DefInt i)
      | OpAtom op -> (
          match op with
          | PlusOp (i1, i2) | MinusOp (i1, i2) ->
              let i1s = eval_int ~m ~cnt i1 in
              let i2s = eval_int ~m ~cnt i2 in
              List.fold (all_combs i1s i2s) ~init:acc ~f:(fun acc pair ->
                  match pair with
                  | Maybe_prim.DefInt x, DefInt y ->
                      Set.add acc
                        (DefInt
                           (match op with
                           | PlusOp _ -> x + y
                           | MinusOp _ -> x - y
                           | _ -> raise Unreachable [@coverage off]))
                  | _ -> Set.add acc Any)
          | _ -> raise Bad_type)
      | LabelResAtom (r, lst) ->
          Set.union acc
            (eval_int
               ~m:(Map.add_exn m ~key:(State.Lstate lst, 0) ~data:r)
               ~cnt r)
      | ExprResAtom (r, est) ->
          Set.union acc
            (eval_int
               ~m:(Map.add_exn m ~key:(State.Estate est, 0) ~data:r)
               ~cnt r)
      | LabelStubAtom lst ->
          if cnt <= 0 then Set.add acc Any
          else
            Set.union acc
              (eval_int ~m ~cnt:(cnt - 1)
                 (Map.find_exn m (State.Lstate lst, 0)))
      | ExprStubAtom est ->
          if cnt <= 0 then Set.add acc Any
          else
            Set.union acc
              (eval_int ~m ~cnt:(cnt - 1)
                 (Map.find_exn m (State.Estate est, 0)))
      | PathCondAtom ((r, b), r') ->
          if
            Set.exists (eval_bool ~m ~cnt r) ~f:(function
              | Maybe_prim.DefBool b' -> Stdlib.(b = b')
              | _ -> false)
          then Set.union acc (eval_int ~m ~cnt r')
          else acc
      | ProjectionAtom (r, l) ->
          fold_res r
            ~init:(Set.empty (module Maybe_prim))
            ~f:
              (fun acc -> function
                | RecordAtom entries -> (
                    match
                      List.find entries ~f:(fun (l', _) -> Stdlib.(l = l'))
                    with
                    | Some (_, r) -> Set.union acc (eval_int ~m ~cnt r)
                    | None -> acc)
                | _ -> raise Bad_type)
      | AssertAtom _ -> failwith "unimplemented")

and eval_bool ?(m = Map.empty (module State)) ?(cnt = 99) r =
  List.fold r
    ~init:(Set.empty (module Maybe_prim))
    ~f:(fun acc a ->
      match a with
      | IntAtom _ | FunAtom _ | RecordAtom _ -> raise Bad_type
      | BoolAtom b -> Set.add acc (DefBool b)
      | OpAtom op -> (
          match op with
          | EqualOp (i1, i2) ->
              let i1s = eval_int ~m ~cnt i1 in
              let i2s = eval_int ~m ~cnt i2 in
              List.fold (all_combs i1s i2s) ~init:acc ~f:(fun acc pair ->
                  match pair with
                  | DefInt x, DefInt y -> Set.add acc (DefBool (Int.equal x y))
                  | _ -> Set.add acc Any)
          | AndOp (b1, b2) | OrOp (b1, b2) ->
              let b1s = eval_bool ~m ~cnt b1 in
              let b2s = eval_bool ~m ~cnt b2 in
              List.fold (all_combs b1s b2s) ~init:acc ~f:(fun acc pair ->
                  match pair with
                  | Maybe_prim.DefBool x, Maybe_prim.DefBool y ->
                      Set.add acc
                        (DefBool
                           (match op with
                           | AndOp _ -> x && y
                           | OrOp _ -> x || y
                           | _ -> raise Unreachable [@coverage off]))
                  | _ -> Set.add acc Any)
          | NotOp b ->
              let bs = eval_bool ~m ~cnt b in
              Set.fold bs ~init:acc ~f:(fun acc b ->
                  match b with
                  | DefBool x -> Set.add acc (DefBool (not x))
                  | _ -> Set.add acc Any)
          | _ -> raise Bad_type)
      | LabelResAtom (r, lst) ->
          Set.union acc
            (eval_bool
               ~m:(Map.add_exn m ~key:(State.Lstate lst, 0) ~data:r)
               ~cnt r)
      | ExprResAtom (r, est) ->
          Set.union acc
            (eval_bool
               ~m:(Map.add_exn m ~key:(State.Estate est, 0) ~data:r)
               ~cnt r)
      | LabelStubAtom lst ->
          if cnt <= 0 then Set.add acc Any
          else
            Set.union acc
              (eval_bool ~m ~cnt:(cnt - 1)
                 (Map.find_exn m (State.Lstate lst, 0)))
      | ExprStubAtom est ->
          if cnt <= 0 then Set.add acc Any
          else
            Set.union acc
              (eval_bool ~m ~cnt:(cnt - 1)
                 (Map.find_exn m (State.Estate est, 0)))
      | PathCondAtom ((_, b), r') ->
          (* can encode path conditions as results *)
          if
            Set.exists (eval_bool ~m ~cnt r) ~f:(function
              | Maybe_prim.DefBool b' -> Stdlib.(b = b')
              | _ -> false)
          then Set.union acc (eval_bool ~m ~cnt r')
          else acc
      | ProjectionAtom (r, l) ->
          fold_res r
            ~init:(Set.empty (module Maybe_prim))
            ~f:
              (fun acc -> function
                | RecordAtom entries -> (
                    match
                      List.find entries ~f:(fun (l', _) -> Stdlib.(l = l'))
                    with
                    | Some (_, r) -> Set.union acc (eval_bool ~m ~cnt r)
                    | None -> acc)
                | _ -> raise Bad_type)
      | InspectionAtom (l, r) ->
          fold_res r
            ~init:(Set.empty (module Maybe_prim))
            ~f:
              (fun acc -> function
                | RecordAtom entries ->
                    Set.add acc
                      (DefBool
                         (List.exists entries ~f:(fun (l', _) ->
                              Stdlib.(l = l'))))
                | _ -> raise Bad_type)
      | AssertAtom _ -> failwith "unimplemented")

let rec process_maybe_bools bs =
  let open Maybe_prim in
  Set.fold_until bs ~init:[]
    ~f:
      (fun acc -> function
        | Any -> Stop [ true; false ]
        | DefBool b -> Continue (b :: acc)
        | DefInt _ -> raise Bad_type)
    ~finish:Fun.id

let cache = Hashtbl.create (module CacheKey)

let print_v_set =
  Set.iter ~f:(fun item -> info (fun m -> m "%s" (State.show item)))

let rec analyze_aux d expr s pi v_set =
  if d > !max_d then max_d := d;
  info (fun m -> m "Max depth so far is: %d" !max_d);
  let cache_entry = (expr, s, pi) in
  match Hashtbl.find cache cache_entry with
  | Some r -> r
  | None ->
      let r =
        match expr with
        | Int i -> Some [ IntAtom i ]
        | Bool b -> Some [ BoolAtom b ]
        | Function (_, _, l) -> Some [ FunAtom (expr, l, s) ]
        | Appl (e, _, l) -> (
            Logs.info (fun m ->
                m "=========== Appl (%a) ============" Interpreter.Pp.pp_expr
                  expr);
            info (fun m -> m "%a" Interpreter.Ast.pp_expr expr);
            info (fun m -> m "At level %d" d);
            info (fun m -> m "sigma: %s" (show_sigma s));
            let ls = l :: s in
            let ls_pruned = prune_sigma ls in
            let state = State.Lstate (l, ls_pruned) in
            info (fun m -> m "Lstate: %d, %s" l (show_sigma ls_pruned));
            log "v_set:";
            print_v_set v_set;
            match
              Set.find v_set ~f:(fun (lstate, _) -> Stdlib.(lstate = state))
            with
            | Some (_, pass) when pass = 1 ->
                (* Application Stub - only actually stub on second pass *)
                info (fun m -> m "Stubbed: %a" Interpreter.Pp.pp_expr expr);
                info (fun m -> m "Stubbed: %a" Interpreter.Ast.pp_expr expr);
                info (fun m ->
                    m "*********** Appl (%a) ************"
                      Interpreter.Pp.pp_expr expr);
                Some [ LabelStubAtom (l, ls_pruned) ]
            | _ ->
                (* Application *)
                info (fun m -> m "Didn't stub: %a" Interpreter.Pp.pp_expr expr);
                info (fun m -> m "Didn't stub: %a" Interpreter.Ast.pp_expr expr);
                info (fun m ->
                    m "Evaluating function being applied: %a"
                      Interpreter.Pp.pp_expr e);
                info (fun m ->
                    m "Evaluating function being applied: %a"
                      Interpreter.Ast.pp_expr e);
                let check_mem = Set.mem v_set (state, 0) in
                info (fun m -> m "state already exists once? %b" check_mem);
                let new_state = (state, if check_mem then 1 else 0) in
                let new_v_set =
                  Set.add (Set.remove v_set (state, 0)) new_state
                in
                let%map r1 = analyze_aux (d + 1) e s pi v_set in
                let r_set =
                  fold_res r1 ~init:empty_choice_set ~f:(fun acc a ->
                      log "Evaluating 1 possible function being applied:";
                      match a with
                      | FunAtom (Function (_, e1, _), _, _)
                      | PathCondAtom (_, [ FunAtom (Function (_, e1, _), _, _) ])
                        -> (
                          Hashset.add s_set ls;
                          info (fun m ->
                              m "Evaluating body of function being applied: %a"
                                Interpreter.Pp.pp_expr e1);
                          match
                            analyze_aux (d + 1) e1 ls_pruned pi new_v_set
                          with
                          | Some ri -> fold_res ri ~init:acc ~f:Set.add
                          | None -> acc)
                      | LabelStubAtom _ | ExprStubAtom _ ->
                          (* provably infeasible path: a singleton stub *)
                          info (fun m ->
                              m
                                "reached a provably infeasible path and got a: \
                                 %a"
                                Grammar.pp_atom a);
                          acc (* TODO: return [] when any atom is stub *)
                      | _ -> raise TypeMismatch)
                in
                info (fun m ->
                    m "*********** Appl (%a) ************"
                      Interpreter.Pp.pp_expr expr);
                [ LabelResAtom (Set.elements r_set, (l, ls_pruned)) ])
        | Var (Ident x, l) -> (
            match get_myfun l with
            | Some (Function (Ident x1, _, l_myfun)) ->
                if String.(x = x1) then (
                  (* Var Local *)
                  info (fun m ->
                      m "=========== Var Local (%s, %d) ============" x l);
                  info (fun m -> m "At level %d" d);
                  info (fun m -> m "sigma: %s" (show_sigma s));
                  if List.length s = 0 then (
                    (Format.printf "Unreachable: Var Local empty sigma_0\n";
                     None)
                    [@coverage off])
                  else
                    let state = (State.Estate (expr, s), 0) in
                    info (fun m ->
                        m "Estate: %a, %s" Interpreter.Pp.pp_expr expr
                          (show_sigma s));
                    log "v_set:";
                    print_v_set v_set;
                    if Set.mem v_set state then (
                      info (fun m -> m "Stubbed: %s" x);
                      (* Var Local Stub *)
                      Some [ ExprStubAtom (expr, s) ])
                    else (
                      info (fun m -> m "Didn't stub: %s" x);
                      let new_v_set = Set.add v_set state in
                      let s_hd, s_tl = (List.hd_exn s, List.tl_exn s) in
                      match get_myexpr s_hd with
                      | Appl (_, e2, l') ->
                          let r_set =
                            log "Stitching stacks:";
                            (* enumerate all matching stacks in the set *)
                            Hashset.fold
                              (fun sigma_i acc ->
                                let sigma_i_hd, sigma_i_tl =
                                  (List.hd_exn sigma_i, List.tl_exn sigma_i)
                                in
                                (* the fact that we can prune away "bad" stacks like this
                                   makes DDE for program analysis superior *)
                                if
                                  sigma_i_hd = l' && starts_with sigma_i_tl s_tl
                                then (
                                  log
                                    "Using matching stack, evaluating Appl \
                                     argument:";
                                  info (fun m ->
                                      m "%a" Interpreter.Pp.pp_expr e2);
                                  match
                                    (* stitch the stack to gain more precision *)
                                    analyze_aux (d + 1) e2 sigma_i_tl pi
                                      new_v_set
                                  with
                                  | Some ri -> fold_res ri ~init:acc ~f:Set.add
                                  | None -> acc)
                                else acc)
                              s_set empty_choice_set
                          in
                          info (fun m ->
                              m "*********** Var Local (%s, %d) ************" x
                                l);
                          Some [ ExprResAtom (Set.elements r_set, (expr, s)) ]
                      | _ -> raise Unreachable [@coverage off]))
                else (
                  (* Var Non-Local *)
                  info (fun m ->
                      m "=========== Var Non-Local (%s, %d) ============" x l);
                  info (fun m -> m "At level %d" d);
                  info (fun m -> m "sigma: %s" (show_sigma s));
                  let state = (State.Estate (expr, s), 0) in
                  info (fun m ->
                      m "Estate: %a, %s" Interpreter.Pp.pp_expr expr
                        (show_sigma s));
                  log "v_set:";
                  print_v_set v_set;
                  if Set.mem v_set state then (
                    info (fun m -> m "Stubbed non-local: %s" x);
                    (* Var Non-Local Stub *)
                    Some [ ExprStubAtom (expr, s) ])
                  else (
                    info (fun m -> m "Didn't stub non-local: %s" x);
                    log "Reading Appl at front of sigma";
                    let new_v_set = Set.add v_set state in
                    match get_myexpr (List.hd_exn s) with
                    | Appl (e1, _, l2) ->
                        log "Function being applied at front of sigma:";
                        info (fun m -> m "%a" Interpreter.Pp.pp_expr e1);
                        info (fun m -> m "%a" Interpreter.Ast.pp_expr e1);
                        let s_tl = List.tl_exn s in
                        let r_set =
                          log "Stitching stacks";
                          log "s_set:";
                          info (fun m -> m "%s" (show_set ()));
                          info (fun m -> m "l2: %d" l2);
                          info (fun m -> m "s.tl: %s" (show_sigma s_tl));
                          (* enumerate all matching stacks in the set *)
                          Hashset.fold
                            (fun si acc ->
                              info (fun m -> m "si: %s" (show_sigma si));
                              let si_hd, si_tl =
                                (List.hd_exn si, List.tl_exn si)
                              in
                              if
                                Stdlib.(si_hd = l2) && starts_with si_tl s_tl
                                (* && Stdlib.(si <> [ 6; 6; 6 ]) *)
                              then (
                                info (fun m ->
                                    m
                                      "Evaluating function being applied at \
                                       front of sigma, using stitched stack %s"
                                      (show_sigma si_tl));
                                match
                                  (* stitch the stack to gain more precision *)
                                  analyze_aux (d + 1) e1 si_tl pi new_v_set
                                with
                                | Some r ->
                                    Set.union acc
                                    @@ fold_res r ~init:acc
                                         ~f:(fun acc fun_atom ->
                                           log
                                             "Evaluating 1 possible function \
                                              being applied:";
                                           info (fun m ->
                                               m "%a" pp_atom fun_atom);
                                           info (fun m ->
                                               m "%a" Grammar.pp_atom fun_atom);
                                           match fun_atom with
                                           | FunAtom
                                               ( Function (Ident x1', _, l1),
                                                 _,
                                                 s1 ) ->
                                               if
                                                 Stdlib.(x1 = x1')
                                                 && l_myfun = l1
                                               then (
                                                 info (fun m ->
                                                     m
                                                       "Re-label %s with label \
                                                        %d and evaluate"
                                                       x l1);
                                                 match
                                                   analyze_aux (d + 1)
                                                     (Var (Ident x, l1))
                                                     s1 pi new_v_set
                                                 with
                                                 | Some ri ->
                                                     fold_res ri ~init:acc
                                                       ~f:Set.add
                                                 | None -> acc)
                                               else acc
                                           | _ -> acc)
                                | _ -> raise Unreachable [@coverage off])
                              else acc)
                            s_set empty_choice_set
                        in
                        info (fun m ->
                            m "*********** Var Non-Local (%s, %d) ************"
                              x l);
                        Some (Set.elements r_set)
                    | _ -> raise Unreachable [@coverage off]))
            | _ -> raise Unreachable [@coverage off])
        (* | If (e, e_true, e_false, l) ->
            let%map r_cond = analyze_aux e s pi v_set in
            r_cond |> eval_bool |> process_maybe_bools
            |> List.map ~f:(fun b ->
                   let path_cond = (r_cond, b) in
                   ( path_cond,
                     analyze_aux
                       (if b then e_true else e_false)
                       s (Some path_cond) v_set ))
            |> List.filter_map ~f:(function
                 | _, None -> None
                 | path_cond, Some r -> Some (path_cond, r))
            |> List.fold
                 ~init:(Set.empty (module PathChoice))
                 ~f:(fun acc (path_cond, r) ->
                   fold_res r ~init:empty_choice_set ~f:Set.add
                   |> Set.elements
                   |> List.map ~f:(fun a -> (path_cond, a))
                   |> List.fold ~init:acc ~f:Set.add)
            |> Set.elements
            (* artificially make `a` not an atom (per spec) *)
            |> List.map ~f:(fun (path_cond, a) -> PathCondAtom (path_cond, [ a ])) *)
        | If (e, e_true, e_false, l) -> (
            (* log "=========== If ============";
               info (fun m -> m "At level %d" d);
               (* log "Evaluating condition:";
                  info (fun m -> m "Condition: %a" Interpreter.Pp.pp_expr e);
                  let%bind r_cond = analyze_aux e s pi v_set in *)
               log "=========== If True ============";
               info (fun m -> m "%a" Interpreter.Pp.pp_expr e_true);
               let%bind r_true = analyze_aux (d + 1) e_true s pi v_set in
               log "*********** If True *************";
               info (fun m -> m "r_true: %a" Utils.pp_res r_true);
               log "=========== If False ============";
               info (fun m -> m "%a" Interpreter.Pp.pp_expr e_false);
               let%map r_false = analyze_aux (d + 1) e_false s pi v_set in
               log "*********** If False *************";
               info (fun m -> m "r_false: %a" Utils.pp_res r_false);
               log "*********** If *************";
               r_true @ r_false *)
            (* TODO: utilize full power of path conditions *)
            let%bind r_cond = analyze_aux (d + 1) e s pi v_set in
            let true_sat = solve_cond r_cond true in
            let pi_true = Some (r_cond, true) in
            let false_sat = solve_cond r_cond false in
            let pi_false = Some (r_cond, false) in
            match (true_sat, false_sat) with
            | true, false ->
                log "=========== If True only ============";
                let%map r_true = analyze_aux (d + 1) e_true s pi_true v_set in
                log "*********** If True only *************";
                [ PathCondAtom ((r_cond, true), r_true) ]
            | false, true ->
                log "=========== If False only ============";
                let%map r_false =
                  analyze_aux (d + 1) e_false s pi_false v_set
                in
                log "*********** If False only *************";
                [ PathCondAtom ((r_cond, false), r_false) ]
            | false, false ->
                log "=========== If True ============";
                let%bind r_true = analyze_aux (d + 1) e_true s pi_true v_set in
                log "*********** If True *************";
                let pc_true = PathCondAtom ((r_cond, true), r_true) in
                log "=========== If False ============";
                let%map r_false =
                  analyze_aux (d + 1) e_false s pi_false v_set
                in
                log "*********** If False *************";
                let pc_false = PathCondAtom ((r_cond, false), r_false) in
                [ pc_true; pc_false ]
            | _ -> raise Unreachable [@coverage off])
        | Plus (e1, e2)
        | Minus (e1, e2)
        | Mult (e1, e2)
        | Equal (e1, e2)
        | And (e1, e2)
        | Or (e1, e2)
        | Ge (e1, e2)
        | Gt (e1, e2)
        | Le (e1, e2)
        | Lt (e1, e2) ->
            let%bind r1 = analyze_aux d e1 s pi v_set in
            let%map r2 = analyze_aux d e2 s pi v_set in
            [
              OpAtom
                (match expr with
                | Plus _ -> PlusOp (r1, r2)
                | Minus _ -> MinusOp (r1, r2)
                | Mult _ -> MultOp (r1, r2)
                | Equal _ -> EqualOp (r1, r2)
                | And _ -> AndOp (r1, r2)
                | Or _ -> OrOp (r1, r2)
                | Ge _ -> GeOp (r1, r2)
                | Gt _ -> GtOp (r1, r2)
                | Le _ -> LeOp (r1, r2)
                | Lt _ -> LtOp (r1, r2)
                | _ -> raise Unreachable [@coverage off]);
            ]
        | Not e ->
            let%map r = analyze_aux d e s pi v_set in
            [ OpAtom (NotOp r) ]
        | Record entries ->
            Some
              [
                RecordAtom
                  (entries
                  |> List.map ~f:(fun (x, ei) ->
                         (x, analyze_aux d ei s pi v_set))
                  |> List.filter_map ~f:(function
                       | _, None -> None
                       | x, Some r -> Some (x, r)));
              ]
        | Projection (e, x) -> (
            let%map r0 = analyze_aux d e s pi v_set in
            (*? any valid r0 must only have one atom *)
            let a = List.hd_exn r0 in
            match a with
            | RecordAtom entries | ExprResAtom ([ RecordAtom entries ], _) -> (
                match List.find entries ~f:(fun (x', _) -> Stdlib.(x = x')) with
                | Some (_, r) -> r
                | None -> raise Unreachable)
            | ExprResAtom _ | ExprStubAtom _ -> [ ProjectionAtom (r0, x) ]
            | _ -> raise Unreachable)
        | Inspection (x, e) ->
            let%map r0 = analyze_aux d e s pi v_set in
            [
              BoolAtom
                (List.for_all r0 ~f:(function
                  | RecordAtom entries ->
                      List.exists entries ~f:(fun (x', _) -> Stdlib.(x = x'))
                  | _ -> true));
            ]
        | LetAssert (id, e1, e2) ->
            let%map r1 = analyze_aux d e1 s pi v_set in
            let r2 = eval_assert e2 id in
            [ AssertAtom (id, r1, r2) ]
        | Let _ -> raise Unreachable [@coverage off]
      in
      Hashtbl.remove cache cache_entry;
      Hashtbl.add_exn cache ~key:cache_entry ~data:r;
      r

let analyze ?(debug = false) ?(verify = true) e =
  is_debug_mode := debug;

  (* let e = transform_let e in *)
  let e = trans_let None None e in
  build_myfun e None;
  log "Program after subst";
  info (fun m -> m "%a" Interpreter.Pp.pp_expr e);
  let r =
    Option.value_exn (analyze_aux 0 e [] None (Set.empty (module State)))
  in

  (* Format.printf "result: %a\n" Grammar.pp_res (Option.value_exn r); *)
  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" @@ show_expr e;
     Format.printf "****** Label Table ******\n";
     Interpreter.Interp.print_myexpr myexpr;
     Format.printf "****** Label Table ******\n\n";
     Hashset.iter (fun s -> Format.printf "%s\n" (show_sigma s)) s_set))
  [@coverage off];

  clean_up ();
  Hashset.clear s_set;

  if verify then verify_result r;

  r
