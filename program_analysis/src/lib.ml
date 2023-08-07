open Core
open Core.Option.Let_syntax
open Interpreter.Ast
open Grammar
open Utils
open Solver

exception Unreachable
exception BadAssert
exception TypeMismatch

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

module CacheKey = struct
  module T = struct
    type t = expr * sigma [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

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
      | AssertAtom _ -> failwith "yo wtf")

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
      | AssertAtom _ -> failwith "yowtf")

let rec process_maybe_bools bs =
  let open Maybe_prim in
  Set.fold_until bs ~init:[]
    ~f:
      (fun acc -> function
        | Any -> Stop [ true; false ]
        | DefBool b -> Continue (b :: acc)
        | DefInt _ -> raise Bad_type)
    ~finish:Fun.id

(* let memo_cache = Hashtbl.create (module CacheKey) *)

let rec analyze_aux expr s pi v_set =
  (* Format.printf "hit aux\n"; *)
  (* match Hashtbl.find memo_cache (expr, s) with
     | Some r ->
         pfl "cache hit";
         r
     | None -> ( *)
  match expr with
  | Int i -> Some [ IntAtom i ]
  | Bool b -> Some [ BoolAtom b ]
  | Function (_, _, l) -> Some [ FunAtom (expr, l, s) ]
  | Appl (e, _, l) -> (
      (* Format.printf "hit appl\n"; *)
      let ls_pruned = prune_sigma (l :: s) in
      let state = State.Lstate (l, ls_pruned) in
      (if !is_debug_mode then pf "Appl: %d\n" l) [@coverage off];
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
                | PathCondAtom (_, [ FunAtom (Function (_, e1, _), _, _) ]) -> (
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
                          if sigma_i_hd = l' && starts_with sigma_i_tl s_tl then
                            match
                              (* stitch the stack to gain more precision *)
                              analyze_aux e2 sigma_i_tl pi (Set.add v_set state)
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
                        Stdlib.(si_hd = l2) && starts_with si_tl (List.tl_exn s)
                      then
                        match
                          (* stitch the stack to gain more precision *)
                          analyze_aux e1 si_tl pi v_set
                        with
                        | Some r ->
                            Set.union acc
                            @@ fold_res r ~init:acc ~f:(fun acc fun_res ->
                                   match fun_res with
                                   | FunAtom (Function (Ident x1', _, l1), _, s1)
                                     when Stdlib.(x1 = x1') && l_myfun = l1 -> (
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
      (* let%bind r_cond = analyze_aux e s pi v_set in
         let%bind r_true = analyze_aux e_true s pi v_set in
         let pc_true = r_true in
         let%map r_false = analyze_aux e_false s pi v_set in
         let pc_false = r_false in
         pc_true @ pc_false *)
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
  | Projection (e, x) ->
      let%map r0 = analyze_aux e s pi v_set in
      [ ProjectionAtom (r0, x) ]
  | Inspection (x, e) ->
      let%map r0 = analyze_aux e s pi v_set in
      [ InspectionAtom (x, r0) ]
  | LetAssert (id, e1, e2) ->
      let%map r1 = analyze_aux e1 s pi v_set in
      let r2 = eval_assert e2 id in
      [ AssertAtom (id, r1, r2) ]
  | Let _ -> raise Unreachable [@coverage off]

let analyze ?(debug = false) ?(verify = true) e =
  is_debug_mode := debug;

  build_myfun e None;
  let e = trans_let None None e in
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
