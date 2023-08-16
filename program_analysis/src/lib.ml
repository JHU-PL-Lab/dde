open Core
open Core.Option.Let_syntax
open Interpreter.Ast
open Grammar
open Utils
open Solver

exception Unreachable
exception BadAssert

let empty_choice_set = Set.empty (module Choice)

let solve_cond r b =
  let solver = Solver.solver in
  Solver.chcs_of_res r;
  let p = Option.value_exn !Solver.entry_decl in
  let chcs = Hash_set.to_list Solver.chcs in
  let rb = zconst "r" bsort in
  Z3.Solver.add solver (([ rb ] |. (p <-- [ rb ]) --> (rb === zbool b)) :: chcs);
  let sat =
    match Z3.Solver.check solver [] with
    | SATISFIABLE ->
        (* let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
           model |> Z3.Model.to_string |> Format.printf "Model:\n%s\n\n"; *)
        (* solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s"; *)
        (* let prog = Format.asprintf "%a" pp_res r in
           Format.printf "if condition: %s\n" prog; *)
        true
    | UNSATISFIABLE -> false
    | UNKNOWN -> failwith "unknown"
  in
  Solver.reset ();
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
  | _ -> raise BadAssert

(** only allows the following forms:
    - arbitrary variable-free arithmetic
    - <var>
    - not <var>
    - <var> <op> <value> *)
let eval_assert e id =
  match e with
  | Bool b -> BoolResultFv b
  | Var (id', _) when Stdlib.(id = id') -> VarResultFv
  | Equal (e1, e2) | Ge (e1, e2) | Gt (e1, e2) | Le (e1, e2) | Lt (e1, e2) -> (
      match e1 with
      | Var (id', _) when Stdlib.(id = id') ->
          let v2 = eval_assert_aux e2 in
          OpResultFv
            (match e with
            | Equal _ -> EqOpFv v2
            | Ge _ -> GeOpFv v2
            | Gt _ -> GtOpFv v2
            | Le _ -> LeOpFv v2
            | Lt _ -> LtOpFv v2
            | _ -> raise Unreachable)
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
      | Var (id', _) when Stdlib.(id = id') -> OpResultFv NotOpFv
      | _ -> eval_assert_aux e')
  | _ -> raise BadAssert

module CacheKey = struct
  module T = struct
    type t = expr * sigma [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

let memo_cache = Hashtbl.create (module CacheKey)

let rec analyze_aux expr s pi v_set =
  match Hashtbl.find memo_cache (expr, s) with
  | Some r ->
      pfl "cache hit";
      r
  | None -> (
      match expr with
      | Int i -> Some [ IntAtom i ]
      | Bool b -> Some [ BoolAtom b ]
      | Function (_, _, l) -> Some [ FunAtom (expr, l, s) ]
      | Appl (e, _, l) -> (
          let ls_pruned = prune_sigma (l :: s) in
          let state = State.Lstate (l, ls_pruned) in
          (if !is_debug_mode then pf "Appl: %d\n" l) [@coverage off];
          (* TODO: id 100 slower than id 10? *)
          match
            Set.find v_set ~f:(function
              | State.Lstate (l', s'), _ when l = l' && Stdlib.(s = s') -> true
              | _ -> false)
          with
          | Some (State.Lstate _, pass) when pass = 1 ->
              (* | Some (State.Lstate _, pass) -> *)
              (* Application Stub - only actually stub on second pass *)
              (* Format.printf "stubbed appl\n"; *)
              Some [ LabelStubAtom (l, ls_pruned) ]
          | _ ->
              (* Application *)
              let%map r = analyze_aux e s pi v_set in
              let r_set =
                fold_res r ~init:empty_choice_set ~f:(fun acc a ->
                    match a with
                    | FunAtom (Function (_, e1, _), _, _)
                    | PathCondAtom (_, [ FunAtom (Function (_, e1, _), _, _) ])
                      -> (
                        Hashset.add s_set (l :: s);
                        let new_state =
                          (state, if Set.mem v_set (state, 0) then 1 else 0)
                        in
                        let v_set = Set.remove v_set (state, 0) in
                        match
                          analyze_aux e1 ls_pruned pi (Set.add v_set new_state)
                        with
                        | Some ri -> fold_res ri ~init:acc ~f:Set.add
                        | None -> acc)
                    | _ -> raise Unreachable [@coverage off])
              in
              [ LabelResAtom (Set.elements r_set, (l, ls_pruned)) ])
      | Var (Ident x, l) -> (
          (* Format.printf "yo\n"; *)
          match get_myfun l with
          | Some (Function (Ident x1, _, l_myfun)) ->
              if String.(x = x1) then (
                (* Var Local *)
                (if !is_debug_mode then
                   Format.printf "Var Local:\n%s, %d\nsigma: %s\nS:\n%s" x l
                     (show_sigma s) (print_set ()))
                [@coverage off];
                if List.length s = 0 then (
                  (Format.printf "Unreachable: Var Local empty sigma_0\n";
                   None)
                  [@coverage off])
                else
                  let state = (State.Estate (expr, s), 0) in
                  if Set.mem v_set state then
                    (* Format.printf "stubbed var\n"; *)
                    (* Var Local Stub *)
                    Some [ ExprStubAtom (expr, s) ]
                  else
                    let s_hd, s_tl = (List.hd_exn s, List.tl_exn s) in
                    let s_hd_expr = get_myexpr s_hd in
                    match s_hd_expr with
                    | Appl (_, e2, l') ->
                        let r_set =
                          (* enumerate all matching stacks in the set *)
                          Hashset.fold
                            (fun sigma_i acc ->
                              let sigma_i_hd, sigma_i_tl =
                                (List.hd_exn sigma_i, List.tl_exn sigma_i)
                              in
                              (* the fact that we can prune away "bad" stacks like this
                                 makes DDE for program analysis superior *)
                              if sigma_i_hd = l' && starts_with sigma_i_tl s_tl
                              then
                                match
                                  (* stitch the stack to gain more precision *)
                                  analyze_aux e2 sigma_i_tl pi
                                    (Set.add v_set state)
                                with
                                | Some ri -> fold_res ri ~init:acc ~f:Set.add
                                | None -> acc
                              else acc)
                            s_set empty_choice_set
                        in
                        Some [ ExprResAtom (Set.elements r_set, (expr, s)) ]
                    | _ -> raise Unreachable [@coverage off])
              else (
                (* Var Non-Local *)
                (if !is_debug_mode then
                   Format.printf "Var Non-Local:\n%s, %d\nsigma: %s\nS:\n%s" x l
                     (show_sigma s) (print_set ()))
                [@coverage off];
                match get_myexpr (List.hd_exn s) with
                | Appl (e1, _, l2) ->
                    let r_set =
                      (* enumerate all matching stacks in the set *)
                      Hashset.fold
                        (fun si acc ->
                          let si_hd, si_tl = (List.hd_exn si, List.tl_exn si) in
                          if
                            Stdlib.(si_hd = l2)
                            && starts_with si_tl (List.tl_exn s)
                          then
                            match
                              (* stitch the stack to gain more precision *)
                              analyze_aux e1 si_tl pi v_set
                            with
                            | Some r ->
                                Set.union acc
                                @@ fold_res r ~init:acc ~f:(fun acc fun_res ->
                                       match fun_res with
                                       | FunAtom
                                           (Function (Ident x1', _, l1), _, s1)
                                         when Stdlib.(x1 = x1') && l_myfun = l1
                                         -> (
                                           match
                                             analyze_aux
                                               (Var (Ident x, l1))
                                               s1 pi v_set
                                           with
                                           | Some ri ->
                                               fold_res ri ~init:acc ~f:Set.add
                                           | None -> acc)
                                       | _ -> acc)
                            | _ -> raise Unreachable [@coverage off]
                          else acc)
                        s_set empty_choice_set
                    in
                    Some (Set.elements r_set)
                | _ -> raise Unreachable [@coverage off])
          | _ -> raise Unreachable [@coverage off])
      | If (e, e_true, e_false, l) -> (
          (* TODO: utilize full power of path conditions *)
          let%bind r_cond = analyze_aux e s pi v_set in
          let true_sat = solve_cond r_cond true in
          let false_sat = solve_cond r_cond false in
          match (true_sat, false_sat) with
          | true, false ->
              (* Format.printf "true branch\n"; *)
              let%map r_true = analyze_aux e_true s pi v_set in
              [ PathCondAtom ((r_cond, true), r_true) ]
          | false, true ->
              (* Format.printf "false branch\n"; *)
              let%map r_false = analyze_aux e_false s pi v_set in
              [ PathCondAtom ((r_cond, false), r_false) ]
          | false, false ->
              (* Format.printf "both branches\n"; *)
              let%bind r_true = analyze_aux e_true s pi v_set in
              let pc_true = PathCondAtom ((r_cond, true), r_true) in
              let%map r_false = analyze_aux e_false s pi v_set in
              let pc_false = PathCondAtom ((r_cond, false), r_false) in
              [ pc_true; pc_false ]
          | _ -> raise Unreachable)
      | Plus (e1, e2)
      | Minus (e1, e2)
      | Equal (e1, e2)
      | And (e1, e2)
      | Or (e1, e2)
      | Ge (e1, e2)
      | Gt (e1, e2)
      | Le (e1, e2)
      | Lt (e1, e2) ->
          let%bind r1 = analyze_aux e1 s pi v_set in
          let%map r2 = analyze_aux e2 s pi v_set in
          [
            OpAtom
              (match expr with
              | Plus _ -> PlusOp (r1, r2)
              | Minus _ -> MinusOp (r1, r2)
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
          let%map r = analyze_aux e s pi v_set in
          [ OpAtom (NotOp r) ]
      | Record entries ->
          Some
            [
              RecordAtom
                (entries
                |> List.map ~f:(fun (x, ei) -> (x, analyze_aux ei s pi v_set))
                |> List.filter_map ~f:(function
                     | _, None -> None
                     | x, Some r -> Some (x, r)));
            ]
      | Projection (e, l) ->
          let%map r0 = analyze_aux e s pi v_set in
          [ ProjectionAtom (r0, l) ]
      | Inspection (l, e) ->
          let%map r0 = analyze_aux e s pi v_set in
          [ InspectionAtom (l, r0) ]
      | LetAssert (id, e1, e2) ->
          let%map r1 = analyze_aux e1 s pi v_set in
          let r2 = eval_assert e2 id in
          [ AssertAtom (r1, r2) ]
      | Let (id, e1, e2) ->
          let e' = Interpreter.Interp.subst id e1 e2 in
          (* Format.printf "after subst:%a\n" Pp.pp_expr e'; *)
          analyze_aux e' s pi v_set
      | LetRec (f, id, e1, e2, l) ->
          let new_var_label = get_next_label () in
          let new_var = Var (f, new_var_label) in
          add_myexpr new_var_label new_var;

          let new_letrec_label = get_next_label () in
          let new_letrec = LetRec (f, id, e1, new_var, new_letrec_label) in
          add_myexpr new_letrec_label new_letrec;

          let body = Interpreter.Interp.subst f new_letrec e1 in
          let func_label = get_next_label () in
          let func = Function (id, body, func_label) in
          add_myexpr func_label func;

          let e' = Interpreter.Interp.subst f func e2 in
          build_myfun e' (get_myfun l);

          analyze_aux e' s pi v_set)

let analyze ?(debug = false) ?(verify = true) e =
  is_debug_mode := debug;

  build_myfun e None;
  let r = Option.value_exn (analyze_aux e [] None (Set.empty (module State))) in

  (* Format.printf "result: %a\n" Grammar.pp_res (Option.value_exn r); *)
  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" @@ show_expr e;
     Format.printf "****** Label Table ******\n";
     print_myexpr myexpr;
     Format.printf "****** Label Table ******\n\n";
     Hashset.iter (fun s -> Format.printf "%s\n" (show_sigma s)) s_set))
  [@coverage off];

  clean_up ();
  Hashset.clear s_set;

  if verify then verify_result r;

  r
