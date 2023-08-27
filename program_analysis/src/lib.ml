open Core
open Core.Option.Let_syntax
open Logs
open Interpreter.Ast
open Grammar
open Utils
open Solver
open Simplifier

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

let print_v_set =
  Set.iter ~f:(fun item -> info (fun m -> m "%s" (State.show item)))

let rec has_stub r st =
  List.exists r ~f:(function
    | IntAtom _ | BoolAtom _ -> false
    | LabelStubAtom lst -> Stdlib.(State.Lstate lst = st)
    | ExprStubAtom est -> Stdlib.(State.Estate est = st)
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2)
        | MinusOp (r1, r2)
        | MultOp (r1, r2)
        | EqualOp (r1, r2)
        | GeOp (r1, r2)
        | GtOp (r1, r2)
        | LeOp (r1, r2)
        | LtOp (r1, r2)
        | AndOp (r1, r2)
        | OrOp (r1, r2) ->
            has_stub r1 st || has_stub r2 st
        | NotOp r -> has_stub r st)
    | LabelResAtom (r, _) | ExprResAtom (r, _) | PathCondAtom (_, r) ->
        (*? new state from LabelResAtom shouldn't matter? *)
        has_stub r st
    | RecordAtom entries -> List.exists entries ~f:(fun (_, r) -> has_stub r st)
    | _ as a ->
        Format.printf "%a\n" Grammar.pp_atom a;
        failwith "nah")

let rec simplify_result =
  let rec simplify_atom a =
    match a with
    | IntAtom _ | BoolAtom _ -> a
    | OpAtom op -> (
        match op with
        | PlusOp (r1, r2) | MinusOp (r1, r2) | MultOp (r1, r2) -> (
            let int_op =
              match op with
              | PlusOp _ -> ( + )
              | MinusOp _ -> ( - )
              | MultOp _ -> ( * )
              | _ -> raise Unreachable
            in
            let r1' = simplify_res r1 in
            let r2' = simplify_res r2 in
            match (r1', r2') with
            | [ IntAtom i1 ], [ IntAtom i2 ] -> IntAtom (int_op i1 i2)
            | ( [ PathCondAtom (pc1, [ IntAtom i1 ]) ],
                [ PathCondAtom (pc2, [ IntAtom i2 ]) ] )
              when Stdlib.(pc1 = pc2) ->
                PathCondAtom (pc1, [ IntAtom (int_op i1 i2) ])
            | ( [ LabelResAtom ([ IntAtom i1 ], st1) ],
                [ LabelResAtom ([ IntAtom i2 ], st2) ] )
              when Stdlib.(st1 = st2) ->
                LabelResAtom ([ IntAtom (int_op i1 i2) ], st1)
            | ( [ ExprResAtom ([ IntAtom i1 ], st1) ],
                [ ExprResAtom ([ IntAtom i2 ], st2) ] )
              when Stdlib.(st1 = st2) ->
                ExprResAtom ([ IntAtom (int_op i1 i2) ], st1)
            | _ ->
                OpAtom
                  (match op with
                  | PlusOp _ -> PlusOp (r1', r2')
                  | MinusOp _ -> MinusOp (r1', r2')
                  | MultOp _ -> MultOp (r1', r2')
                  | _ -> raise Unreachable))
        | EqualOp (r1, r2)
        | GeOp (r1, r2)
        | GtOp (r1, r2)
        | LeOp (r1, r2)
        | LtOp (r1, r2) -> (
            let int_op =
              match op with
              | EqualOp _ -> ( = )
              | GeOp _ -> ( >= )
              | GtOp _ -> ( > )
              | LeOp _ -> ( <= )
              | LtOp _ -> ( < )
              | _ -> raise Unreachable
            in
            let r1' = simplify_res r1 in
            let r2' = simplify_res r2 in
            match (r1', r2') with
            | [ IntAtom i1 ], [ IntAtom i2 ] -> BoolAtom (int_op i1 i2)
            | ( [ PathCondAtom (pc1, [ IntAtom i1 ]) ],
                [ PathCondAtom (pc2, [ IntAtom i2 ]) ] )
              when Stdlib.(pc1 = pc2) ->
                PathCondAtom (pc1, [ BoolAtom (int_op i1 i2) ])
            | ( [ LabelResAtom ([ IntAtom i1 ], st1) ],
                [ LabelResAtom ([ IntAtom i2 ], st2) ] )
              when Stdlib.(st1 = st2) ->
                LabelResAtom ([ BoolAtom (int_op i1 i2) ], st1)
            | ( [ ExprResAtom ([ IntAtom i1 ], st1) ],
                [ ExprResAtom ([ IntAtom i2 ], st2) ] )
              when Stdlib.(st1 = st2) ->
                ExprResAtom ([ BoolAtom (int_op i1 i2) ], st1)
            | _ ->
                OpAtom
                  (match op with
                  | EqualOp _ -> EqualOp (r1', r2')
                  | GeOp _ -> GeOp (r1', r2')
                  | GtOp _ -> GtOp (r1', r2')
                  | LeOp _ -> LeOp (r1', r2')
                  | LtOp _ -> LtOp (r1', r2')
                  | _ -> raise Unreachable))
        | AndOp (r1, r2) | OrOp (r1, r2) -> (
            let bool_op =
              match op with
              | AndOp _ -> ( && )
              | OrOp _ -> ( || )
              | _ -> raise Unreachable
            in
            let r1' = simplify_res r1 in
            let r2' = simplify_res r2 in
            match (r1', r2') with
            | [ BoolAtom b1 ], [ BoolAtom b2 ] -> BoolAtom (bool_op b1 b2)
            | ( [ PathCondAtom (pc1, [ BoolAtom b1 ]) ],
                [ PathCondAtom (pc2, [ BoolAtom b2 ]) ] )
              when Stdlib.(pc1 = pc2) ->
                PathCondAtom (pc1, [ BoolAtom (bool_op b1 b2) ])
            | ( [ LabelResAtom ([ BoolAtom b1 ], st1) ],
                [ LabelResAtom ([ BoolAtom b2 ], st2) ] )
              when Stdlib.(st1 = st2) ->
                LabelResAtom ([ BoolAtom (bool_op b1 b2) ], st1)
            | ( [ ExprResAtom ([ BoolAtom b1 ], st1) ],
                [ ExprResAtom ([ BoolAtom b2 ], st2) ] )
              when Stdlib.(st1 = st2) ->
                ExprResAtom ([ BoolAtom (bool_op b1 b2) ], st1)
            | _ ->
                OpAtom
                  (match op with
                  | AndOp _ -> AndOp (r1', r2')
                  | OrOp _ -> OrOp (r1', r2')
                  | _ -> raise Unreachable))
        | _ ->
            Format.printf "%a\n" pp_op op;
            failwith "unimplemented")
    | LabelResAtom (r, st) -> (
        let r' = simplify_res r in
        match r' with
        | [ a ] when not (has_stub r' (State.Lstate st)) -> a
        | _ -> LabelResAtom (r', st))
    | ExprResAtom (r, st) -> (
        let r' = simplify_res r in
        match r' with
        | [ a ] when not (has_stub r' (State.Estate st)) -> a
        | _ -> ExprResAtom (r', st))
    | AssertAtom (id, r, rv) -> AssertAtom (id, simplify_res r, rv)
    | PathCondAtom ((r, b), r0) ->
        PathCondAtom ((simplify_res r, b), simplify_res r0)
    | RecordAtom entries ->
        RecordAtom (List.map entries ~f:(fun (x, r) -> (x, simplify_res r)))
    | ProjectionAtom (r, x) ->
        let r' = simplify_res r in
        if List.length r' = 1 then
          match List.hd_exn r' with
          | RecordAtom entries -> (
              match List.find entries ~f:(fun (id, _) -> Stdlib.(id = x)) with
              | Some (_, r) -> List.hd_exn r
              | None -> failwith "runtime error")
          | _ -> ProjectionAtom (r', x)
          (* Format.printf "%a\n" pp_atom a;
             raise Unreachable *)
        else ProjectionAtom (r', x)
    | InspectionAtom (x, r) ->
        let r' = simplify_res r in
        if List.length r' = 1 then
          match List.hd_exn r' with
          | RecordAtom entries ->
              BoolAtom (List.exists entries ~f:(fun (id, _) -> Stdlib.(id = x)))
          | _ -> InspectionAtom (x, r')
          (* Format.printf "%a\n" pp_atom a;
             failwith "runtime error") *)
        else InspectionAtom (x, r')
    | LabelStubAtom _ | ExprStubAtom _ -> a
    | _ ->
        Format.printf "%a\n" Grammar.pp_atom a;
        failwith "unimplemented"
  and simplify_res r = List.map r ~f:simplify_atom in
  simplify_res

(* let cache = Hashtbl.create (module CacheKey) *)

let show_cache_entry (e, s, pi) =
  let pi_s =
    if Option.is_some pi then
      let r, b = Option.value_exn pi in
      Format.asprintf "Some (%a, %b)" pp_res r b
    else "None"
  in
  Format.asprintf "(e: %a, sigma: %s, pi: %s)" Interpreter.Pp.pp_expr e
    (show_sigma s) pi_s

let show_cache cache expr =
  Hashtbl.fold cache ~init:"" ~f:(fun ~key ~data acc ->
      let e, _, _ = key in
      if Stdlib.(e = expr) then
        Format.asprintf "%s\n%s -> %a" acc (show_cache_entry key) pp_res
          (Option.value_exn data)
      else acc)

let rec analyze_aux d expr s pi v_set =
  if d > !max_d then max_d := d;
  log "Began recursive call to execution";
  info (fun m -> m "Max depth so far is: %d" !max_d);
  info (fun m -> m "expr: %a" Interpreter.Pp.pp_expr expr);
  info (fun m -> m "sigma: %s" (show_sigma s));
  (* let cache_entry = (expr, s, pi) in
     (if Option.is_some pi then
        let cond, b = Option.value_exn pi in
        info (fun m -> m "pi: %a = %b" pp_res cond b));
     log "Cache entries with matching expression (sigma and pi may differ):";
     let cache_s = show_cache cache expr in
     info (fun m -> m "%s" cache_s);
     log "Attempt to cache only not at Var";
     match Hashtbl.find cache cache_entry with
     | Some r when match expr with Var _ -> false | _ -> false ->
         log "Cache hit";
         r
     | _ ->
         log "Cache miss"; *)
  let r =
    match expr with
    | Int i -> Some [ IntAtom i ]
    | Bool b -> Some [ BoolAtom b ]
    | Function (_, _, l) -> Some [ FunAtom (expr, l, s) ]
    | Appl (e, _, l) -> (
        info (fun m ->
            m "[Level %d] =========== Appl (%a) ============" d
              Interpreter.Pp.pp_expr expr);
        info (fun m -> m "%a" Interpreter.Ast.pp_expr expr);
        info (fun m -> m "At level %d" d);
        info (fun m -> m "sigma: %s" (show_sigma s));
        let ls = l :: s in
        let ls_pruned = prune_sigma ls in
        info (fun m -> m "ls_pruned: %s" (show_sigma ls_pruned));
        let st = (l, ls_pruned) in
        let lst = State.Lstate st in
        info (fun m -> m "Lstate: %d, %s" l (show_sigma ls_pruned));
        log "v_set:";
        print_v_set v_set;
        match Set.find v_set ~f:(fun (lstate, _) -> Stdlib.(lstate = lst)) with
        | Some (_, pass) when pass = 1 ->
            (* Application Stub - only actually stub on second pass *)
            info (fun m -> m "Stubbed: %a" Interpreter.Pp.pp_expr expr);
            info (fun m -> m "Stubbed: %a" Interpreter.Ast.pp_expr expr);
            info (fun m ->
                m "[Level %d] *********** Appl (%a) ************" d
                  Interpreter.Pp.pp_expr expr);
            Some [ LabelStubAtom st ]
        | _ ->
            (* Application *)
            info (fun m -> m "Didn't stub: %a" Interpreter.Pp.pp_expr expr);
            info (fun m -> m "Didn't stub: %a" Interpreter.Ast.pp_expr expr);
            info (fun m ->
                m "Evaluating function being applied: %a" Interpreter.Pp.pp_expr
                  e);
            info (fun m ->
                m "Evaluating function being applied: %a"
                  Interpreter.Ast.pp_expr e);
            let check_mem = Set.mem v_set (lst, 0) in
            info (fun m -> m "state already exists once? %b" check_mem);
            let new_state = (lst, if check_mem then 1 else 0) in
            let new_v_set = Set.add (Set.remove v_set (lst, 0)) new_state in
            let%map r1 = analyze_aux (d + 1) e s pi v_set in
            let r1 = simplify r1 in
            let r2 =
              List.fold r1 ~init:empty_choice_set ~f:(fun acc a ->
                  log "Evaluating 1 possible function being applied:";
                  match a with
                  | FunAtom (Function (_, e1, _), _, _)
                  (* | PathCondAtom (_, [ FunAtom (Function (_, e1, _), _, _) ])
                     | LabelResAtom ([ FunAtom (Function (_, e1, _), _, _) ], _)
                     | ExprResAtom ([ FunAtom (Function (_, e1, _), _, _) ], _) *)
                    -> (
                      Hashset.add s_set ls;
                      info (fun m ->
                          m "Evaluating body of function being applied: %a"
                            Interpreter.Pp.pp_expr e1);
                      match analyze_aux (d + 1) e1 ls_pruned pi new_v_set with
                      | Some ri -> List.fold ri ~init:acc ~f:Set.add
                      | None ->
                          Format.printf "ayo None\n";
                          acc)
                  | LabelStubAtom _ | ExprStubAtom _ ->
                      (* provably infeasible path: a singleton stub *)
                      info (fun m ->
                          m "reached a provably infeasible path and got a: %a"
                            Grammar.pp_atom a);
                      acc (* TODO: return [] when any atom is stub *)
                  | _ ->
                      info (fun m ->
                          m "[Appl] reached a funky result: %a" Utils.pp_atom a);
                      info (fun m ->
                          m "[Appl] reached a funky result: %a" Grammar.pp_atom
                            a);
                      acc
                  (* raise TypeMismatch *))
            in
            info (fun m ->
                m "[Level %d] *********** Appl (%a) ************" d
                  Interpreter.Pp.pp_expr expr);
            [ LabelResAtom (Set.elements r2, st) ])
    | Var (Ident x, l) -> (
        info (fun m ->
            m "[Level %d] =========== Var (%s, %d) ============" d x l);
        let st = (expr, s) in
        let est = (State.Estate st, 0) in
        info (fun m ->
            m "Estate: %a, %s" Interpreter.Ast.pp_expr expr (show_sigma s));
        log "v_set:";
        print_v_set v_set;
        if Set.mem v_set est then (
          (* Var Stub *)
          info (fun m -> m "Stubbed: %s" x);
          info (fun m ->
              m "[Level %d] *********** Var (%s, %d) ************" d x l);
          Some [ ExprStubAtom st ])
        else
          let new_v_set = Set.add v_set est in
          info (fun m -> m "Didn't stub: %s" x);
          match get_myfun l with
          | Some (Function (Ident x1, _, l_myfun)) ->
              if String.(x = x1) then (
                (* Var Local *)
                info (fun m ->
                    m "[Level %d] =========== Var Local (%s, %d) ============" d
                      x l);
                info (fun m -> m "At level %d" d);
                info (fun m -> m "sigma: %s" (show_sigma s));
                if List.length s = 0 then (
                  (Format.printf "Unreachable: Var Local empty sigma_0\n";
                   None)
                  [@coverage off])
                else
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
                            if sigma_i_hd = l' && starts_with sigma_i_tl s_tl
                            then (
                              log
                                "Using matching stack, evaluating Appl \
                                 argument:";
                              info (fun m -> m "%a" Interpreter.Pp.pp_expr e2);
                              info (fun m -> m "%a" Interpreter.Ast.pp_expr e2);
                              match
                                (* stitch the stack to gain more precision *)
                                analyze_aux (d + 1) e2 sigma_i_tl pi new_v_set
                              with
                              | Some ri -> List.fold ri ~init:acc ~f:Set.add
                              | None -> acc)
                            else acc)
                          s_set empty_choice_set
                      in
                      info (fun m ->
                          m
                            "[Level %d] *********** Var Local (%s, %d) \
                             ************"
                            d x l);
                      info (fun m ->
                          m "[Level %d] *********** Var (%s, %d) ************" d
                            x l);
                      Some [ ExprResAtom (Set.elements r_set, st) ]
                  | _ -> raise Unreachable [@coverage off])
              else (
                (* Var Non-Local *)
                info (fun m ->
                    m
                      "[Level %d] =========== Var Non-Local (%s, %d) \
                       ============"
                      d x l);
                info (fun m -> m "At level %d" d);
                info (fun m -> m "sigma: %s" (show_sigma s));
                log "Reading Appl at front of sigma";
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
                          let si_hd, si_tl = (List.hd_exn si, List.tl_exn si) in
                          if
                            Stdlib.(si_hd = l2) && starts_with si_tl s_tl
                            (* && Stdlib.(si <> [ 6; 6; 6 ]) *)
                          then (
                            info (fun m ->
                                m
                                  "Evaluating function being applied at front \
                                   of sigma, using stitched stack %s"
                                  (show_sigma si_tl));
                            match
                              (* stitch the stack to gain more precision *)
                              analyze_aux (d + 1) e1 si_tl pi new_v_set
                            with
                            | Some r1 ->
                                List.fold r1 ~init:acc ~f:(fun acc fun_atom ->
                                    log
                                      "Visiting 1 possible function being \
                                       applied:";
                                    info (fun m -> m "%a" pp_atom fun_atom);
                                    info (fun m ->
                                        m "%a" Grammar.pp_atom fun_atom);
                                    match fun_atom with
                                    | FunAtom
                                        (Function (Ident x1', _, l1), _, s1)
                                    (* | LabelResAtom
                                        ( [
                                            FunAtom
                                              ( Function (Ident x1', _, l1),
                                                _,
                                                s1 );
                                          ],
                                          _ ) *) ->
                                        if Stdlib.(x1 = x1') && l_myfun = l1
                                        then (
                                          info (fun m ->
                                              m
                                                "Re-label %s with label %d and \
                                                 evaluate"
                                                x l1);
                                          match
                                            analyze_aux (d + 1)
                                              (Var (Ident x, l1))
                                              s1 pi new_v_set
                                          with
                                          | Some ri ->
                                              List.fold ri ~init:acc ~f:Set.add
                                          | None -> acc)
                                        else acc
                                    | _ ->
                                        info (fun m ->
                                            m
                                              "[Var Non-Local] reached an \
                                               empty result: %a"
                                              Grammar.pp_atom fun_atom);
                                        acc)
                            | _ -> raise Unreachable [@coverage off])
                          else acc)
                        s_set empty_choice_set
                    in
                    info (fun m ->
                        m
                          "[Level %d] *********** Var Non-Local (%s, %d) \
                           ************"
                          d x l);
                    info (fun m ->
                        m "[Level %d] *********** Var (%s, %d) ************" d x
                          l);
                    Some (Set.elements r_set)
                | _ -> raise Unreachable [@coverage off])
          | _ -> raise Unreachable [@coverage off])
    | If (e, e_true, e_false, l) -> (
        (* TODO: utilize full power of path conditions *)
        log "=========== If ============";
        let%bind r_cond = analyze_aux (d + 1) e s pi v_set in
        (* Logs.info (fun m -> m "r_cond: %a" Grammar.pp_res r_cond); *)
        let r_cond = simplify r_cond in
        (* let r_cond = simplify_result r_cond in *)
        (* Logs.info (fun m -> m "r_cond simplified: %a" Utils.pp_res r_cond); *)
        let true_sat = solve_cond r_cond true in
        let pc_true = (r_cond, true) in
        let false_sat = solve_cond r_cond false in
        let pc_false = (r_cond, false) in
        match (true_sat, false_sat) with
        | true, false ->
            log "=========== If True only ============";
            info (fun m -> m "Evaluating: %a" Interpreter.Pp.pp_expr e_true);
            let%map r_true =
              analyze_aux (d + 1) e_true s (Some pc_true) v_set
            in
            log "*********** If True only *************";
            log "*********** If ************";
            [ PathCondAtom (pc_true, r_true) ]
        | false, true ->
            log "=========== If False only ============";
            info (fun m -> m "Evaluating: %a" Interpreter.Pp.pp_expr e_false);
            let%map r_false =
              analyze_aux (d + 1) e_false s (Some pc_false) v_set
            in
            log "*********** If False only *************";
            log "*********** If ************";
            [ PathCondAtom (pc_false, r_false) ]
        | false, false ->
            log "=========== If both  ============";
            log "=========== If True ============";
            info (fun m -> m "Evaluating: %a" Interpreter.Pp.pp_expr e_true);
            let%bind r_true =
              analyze_aux (d + 1) e_true s (Some pc_true) v_set
            in
            log "*********** If True *************";
            let pc_true = PathCondAtom (pc_true, r_true) in
            log "=========== If False ============";
            info (fun m -> m "Evaluating: %a" Interpreter.Pp.pp_expr e_false);
            let%map r_false =
              analyze_aux (d + 1) e_false s (Some pc_false) v_set
            in
            log "*********** If False *************";
            log "*********** If both  *************";
            log "*********** If ************";
            let pc_false = PathCondAtom (pc_false, r_false) in
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
        info (fun m -> m "LHS: %a!" pp_res r1);
        info (fun m ->
            m "e2: %a | RHS: %a!" Interpreter.Pp.pp_expr e2 pp_res r2);
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
              |> List.map ~f:(fun (x, ei) -> (x, analyze_aux d ei s pi v_set))
              |> List.filter_map ~f:(function
                   | _, None -> None
                   | x, Some r -> Some (x, r)));
          ]
    | Projection (e, x) ->
        let%map r0 = analyze_aux d e s pi v_set in
        [ ProjectionAtom (r0, x) ]
    | Inspection (x, e) ->
        let%map r0 = analyze_aux d e s pi v_set in
        [ InspectionAtom (x, r0) ]
    | LetAssert (id, e1, e2) ->
        let%map r1 = analyze_aux d e1 s pi v_set in
        let r2 = eval_assert e2 id in
        [ AssertAtom (id, r1, r2) ]
    | Let _ -> raise Unreachable [@coverage off]
  in
  (* let cache_entry_s = show_cache_entry cache_entry in
     log "Caching execution...";
     info (fun m -> m "Looking up existing value at key %s" cache_entry_s);
     (match Hashtbl.find cache cache_entry with
     | Some r ->
         info (fun m -> m "Found existing result %a" pp_res (Option.value_exn r))
     | None -> info (fun m -> m "Didn't find existing result"));
     log "Remove any existing cache entry";
     Hashtbl.remove cache cache_entry;
     info (fun m ->
         m "Add new cache entry with value %a" pp_res (Option.value_exn r));
     Hashtbl.add_exn cache ~key:cache_entry ~data:r; *)
  let%map r = r in
  simplify r
(* r *)

let analyze ?(debug = false) ?(verify = true) ?(test_num = 0) e =
  is_debug_mode := debug;

  let e = transform_let e in
  (* let e = trans_let None None e in *)
  (* Format.printf "e: %a\n" Interpreter.Ast.pp_expr e; *)
  build_myfun e None;
  log "Program after subst";
  info (fun m -> m "%a" Interpreter.Pp.pp_expr e);
  let r =
    Option.value_exn (analyze_aux 0 e [] None (Set.empty (module State)))
  in

  (* Format.printf "result: %a\n" Grammar.pp_res r; *)
  let r = simplify r in

  (* let r = simplify_result r in *)
  dot_of_result test_num r;

  (* Format.printf "simplifiedresult: %a\n" Grammar.pp_res simplified_r; *)
  (* Logs.info (fun m -> m "result: %a" Utils.pp_res r); *)
  (* Logs.info (fun m -> m "result: %a" Grammar.pp_res r); *)
  (* Logs.info (fun m -> m "simplified result: %a" Utils.pp_res r');
     Logs.info (fun m -> m "simplified result: %a" Grammar.pp_res r'); *)
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

(* TODO: DDE kinda similar to mCFA *)
(* TODO: performance bottleneck with checking if two sets are same if we were to cache with S set. Zack's library to give unique id for a set *)
(* TODO: fancy caching scheme to tell how to catch up (timestamped cache entries) *)

(* TODO: make rules more clear *)
(* TODO: what's the relationship between judgements holding: e and e1, x twice deep in e1 in Var Non-Local *)
