open Core
open Logs
open Interp.Ast
open Utils
open Utils.Atom
open Utils
open Solver
open Simplifier
open Exns

(* max recursion depth ever reached by execution *)
let max_d = ref 0

let solve_cond r b =
  let solver = Z3.Solver.mk_solver_s ctx "HORN" in
  let (), { chcs; entry_decl; _ } = State.run (Solver.chcs_of_res r) in
  let chcs = Set.elements chcs in
  let p = Option.value_exn entry_decl in
  let rb = zconst "r" bsort in
  let manual = [ rb ] |. (p <-- [ rb ]) --> (rb === zbool b) in
  Z3.Solver.add solver (manual :: chcs);

  match Z3.Solver.check solver [] with
  | SATISFIABLE -> true
  | UNSATISFIABLE | UNKNOWN -> false

let rec eval_assert_aux e =
  match e with
  | Int i -> IntResFv i
  | Bool b -> BoolResFv b
  | Plus (e1, e2)
  | Minus (e1, e2)
  | Eq (e1, e2)
  | Ge (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Lt (e1, e2) -> (
      match (eval_assert_aux e1, eval_assert_aux e2) with
      | IntResFv i1, IntResFv i2 -> (
          match e with
          | Plus _ -> IntResFv (i1 + i2)
          | Minus _ -> IntResFv (i1 - i2)
          | Eq _ -> BoolResFv (i1 = i2)
          | Ge _ -> BoolResFv (i1 >= i2)
          | Gt _ -> BoolResFv (i1 > i2)
          | Le _ -> BoolResFv (i1 <= i2)
          | Lt _ -> BoolResFv (i1 < i2)
          | _ -> raise Unreachable)
      | _ -> raise Unreachable)
  | And (e1, e2) | Or (e1, e2) -> (
      match (eval_assert_aux e1, eval_assert_aux e2) with
      | BoolResFv b1, BoolResFv b2 -> (
          match e with
          | And _ -> BoolResFv (b1 && b2)
          | Or _ -> BoolResFv (b1 || b2)
          | _ -> raise Unreachable)
      | _ -> raise Unreachable)
  | Not e -> (
      match eval_assert_aux e with
      | BoolResFv b -> BoolResFv (not b)
      | _ -> raise Unreachable)
  | _ ->
      Format.printf "%a" Interp.Pp.pp_expr e;
      raise Bad_assert

(** we only allow the following forms:
    - arbitrary variable-free arithmetic
    - <var>
    - not <var>
    - <var> <op> <value> *)
let eval_assert e id =
  match e with
  | Bool b -> BoolResFv b
  | Var (id', _) when Stdlib.(id = id') -> VarResFv id'
  | Eq (e1, e2) | Ge (e1, e2) | Gt (e1, e2) | Le (e1, e2) | Lt (e1, e2) -> (
      match e1 with
      | Var (id', _) when Stdlib.(id = id') -> (
          let v1 = VarResFv id' in
          let v2 = eval_assert_aux e2 in
          match e with
          | Eq _ -> EqResFv (v1, v2)
          | Ge _ -> GeResFv (v1, v2)
          | Gt _ -> GtResFv (v1, v2)
          | Le _ -> LeResFv (v1, v2)
          | Lt _ -> LtResFv (v1, v2)
          | _ -> raise Unreachable)
      | Proj (e1, x) -> failwith "Not supported"
      | _ -> (
          let v1, v2 = (eval_assert_aux e1, eval_assert_aux e2) in
          match (v1, v2) with
          | IntResFv i1, IntResFv i2 -> (
              match e with
              | Eq _ -> BoolResFv (i1 = i2)
              | Ge _ -> BoolResFv (i1 >= i2)
              | Gt _ -> BoolResFv (i1 > i2)
              | Le _ -> BoolResFv (i1 <= i2)
              | Lt _ -> BoolResFv (i1 < i2)
              | _ -> raise Unreachable)
          | _ -> raise Bad_assert))
  | Not e' -> (
      match e' with
      | Var (id', _) when Stdlib.(id = id') -> NotResFv (VarResFv id')
      | _ -> eval_assert_aux e')
  | _ -> raise Bad_assert

let log_v_set = Set.iter ~f:(fun st -> debug (fun m -> m "%s" (V_key.show st)))

let rec fold_res_app ~init ~f l sigma d =
  List.fold ~init ~f:(fun acc a ->
      debug (fun m ->
          m "[Level %d] [App] Evaluating 1 possible function being applied:" d);
      debug (fun m -> m "%a" pp a);
      match a with
      | FunAtom (Fun (_, e1, _), _, _) -> f acc e1
      | LStubAtom _ | EStubAtom _ -> acc
      | LResAtom (r, _) | EResAtom (r, _) | PathCondAtom (_, r) ->
          fold_res_app ~init:acc ~f l sigma d r
      | _ ->
          Format.printf "%a\n" pp a;
          failwith "unimplemented")

let rec fold_res_var ~init ~f expr sigma d r =
  List.fold r ~init ~f:(fun acc a ->
      debug (fun m -> m "r1 length: %d" (List.length r));
      debug (fun m -> m "[Level %d] Visiting 1 possible function for e1:" d);
      debug (fun m -> m "%a" pp a);
      match a with
      | FunAtom (Fun (Ident x1, _, l1), _, sigma1) -> f acc x1 l1 sigma1
      | LStubAtom _ | EStubAtom _ -> acc
      | LResAtom (r, _) | EResAtom (r, _) ->
          fold_res_var ~init:acc ~f expr sigma d r
      | _ ->
          Format.printf "%a\n" pp a;
          failwith "unimplemented")

let rec exists_lone_stub v v' =
  List.exists ~f:(function
    | LStubAtom ((l, sigma) as st) ->
        (not
           (Set.exists v ~f:(function
             (* TODO: remove sigma *)
             | V_key.Lstate (l', sigma', _) ->
                 l = l' && compare_sigma sigma sigma' = 0
             | _ -> false)))
        && not (Set.mem v' (St.Lstate st))
    | EStubAtom ((e, sigma) as st) ->
        (not
           (Set.exists v ~f:(function
             | V_key.Estate (e', sigma', _) ->
                 compare_expr e e' = 0 && compare_sigma sigma sigma' = 0
             | _ -> false)))
        && not (Set.mem v' (St.Estate st))
    | LResAtom (r, st) -> exists_lone_stub v (Set.add v' (St.Lstate st)) r
    | EResAtom (r, st) -> exists_lone_stub v (Set.add v' (St.Estate st)) r
    | PlusAtom (r1, r2)
    | MinusAtom (r1, r2)
    | MultAtom (r1, r2)
    | EqAtom (r1, r2)
    | GeAtom (r1, r2)
    | GtAtom (r1, r2)
    | LeAtom (r1, r2)
    | LtAtom (r1, r2)
    | AndAtom (r1, r2)
    | OrAtom (r1, r2) ->
        exists_lone_stub v v' r1 || exists_lone_stub v v' r2
    | NotAtom r -> exists_lone_stub v v' r
    | _ -> false)

let elim_stub r label =
  if exists_stub r label then
    let bases =
      List.filter_map r ~f:(fun a ->
          match a with
          | RecAtom _ when not (exists_stub [ a ] label) -> Some a
          | ProjAtom (([ RecAtom es ] as r), Ident key)
            when not (exists_stub r label) -> (
              match
                List.find es ~f:(fun (Ident key', _) -> String.(key = key'))
              with
              | Some (_, [ a ]) -> Some a
              | _ -> raise Runtime_error)
          | FunAtom _ -> Some a
          | _ -> None)
    in
    let r' =
      List.concat_map r ~f:(function
        | ProjAtom ([ EStubAtom st ], Ident key) when St.(label = Estate st) ->
            List.concat_map bases ~f:(fun base ->
                match base with
                | RecAtom es -> (
                    match
                      List.find es ~f:(fun (Ident key', _) ->
                          String.(key = key'))
                    with
                    | Some (_, r) -> r
                    | None -> [])
                | _ -> raise Runtime_error)
        | EStubAtom st when St.(label = Estate st) -> []
        | a -> [ a ])
    in
    r'
  else r

open ReaderState
open ReaderState.Let_syntax

let cache key data =
  let%bind { c; _ } = get () in
  let%bind () = set_cache (Map.add_exn (Map.remove c key) ~key ~data) in
  debug (fun m ->
      m "[Cache] Add: %s\n->\n%s" (Cache_key.show key) (Res.show data));
  return data

let rec analyze_aux ~caching d expr sigma pi : Res.t T.t =
  let%bind { v; _ } = ask () in
  let%bind { c; s; sids; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  let%bind r =
    match expr with
    | Int i -> return [ IntAtom i ]
    | Bool b -> return [ BoolAtom b ]
    | Fun (_, _, l) -> return [ FunAtom (expr, l, sigma) ]
    | App (e, _, l) -> (
        let cache_key = Cache_key.Lkey (l, sigma, vid, sid, pi) in
        match Map.find c cache_key with
        | Some r when caching ->
            debug (fun m ->
                m "[Level %d] Hit: %s\n->\n%s" d (Cache_key.show cache_key)
                  (Res.show r));
            return r
        | _ ->
            info (fun m ->
                m "[Level %d] === App (%a, %d) ===" d Interp.Pp.pp_expr expr l);
            let cycle_label = (l, sigma) in
            let v_state = V_key.Lstate (l, sigma, sid) in
            (* let v_state = V_key.Lstate (l, pruned_sigma', s) in *)
            if Set.mem v v_state then (
              debug (fun m -> m "Stubbed");
              info (fun m ->
                  m "[Level %d] *** App (%a) ***" d Interp.Pp.pp_expr expr);
              cache cache_key [ LStubAtom cycle_label ])
            else (
              (* App *)
              debug (fun m -> m "Didn't stub");
              debug (fun m -> m "sigma: %a" Sigma.pp sigma);
              let sigma' = l :: sigma in
              let pruned_sigma' = prune_sigma sigma' in
              debug (fun m -> m "sigma_pruned': %a" Sigma.pp pruned_sigma');
              debug (fun m ->
                  m "Evaluating function being applied: %a" Interp.Pp.pp_expr e);
              (* we don't remember whatever this subtree visited *)
              let%bind r1 = analyze_aux ~caching d e sigma pi in
              debug (fun m -> m "[App] r1 length: %d" (List.length r1));
              let%bind { s = s1; _ } = get () in
              let v_state_s = Set.add s1 pruned_sigma' in
              (* let v_state_s = Set.add s1 sigma' in *)
              let%bind () = set_s v_state_s in
              let%bind v_state_sid = get_sid v_state_s in
              let v_new = V_key.Lstate (l, sigma, v_state_sid) in
              let%bind r2 =
                fold_res_app ~init:(return empty_res) l sigma d r1
                  ~f:(fun acc e1 ->
                    debug (fun m ->
                        m "[App] Evaluating body of function being applied: %a"
                          Interp.Pp.pp_expr e1);
                    let%bind rs = acc in
                    let%bind r0 =
                      local d
                        (fun ({ v; _ } as env) ->
                          { env with v = Set.add v v_new })
                        (analyze_aux ~caching d e1 pruned_sigma' pi)
                    in
                    return (List.fold r0 ~init:rs ~f:Set.add))
              in
              let r2 = Set.elements r2 in
              let r2 = elim_stub r2 (St.Lstate cycle_label) in
              info (fun m ->
                  m "[Level %d] *** App (%a) ***" d Interp.Pp.pp_expr expr);
              cache cache_key [ LResAtom (r2, cycle_label) ]))
    | Var (Ident x, l) -> (
        let cache_key = Cache_key.Ekey (expr, sigma, vid, sid, pi) in
        match Map.find c cache_key with
        | Some r when caching ->
            debug (fun m ->
                m "[Level %d] Hit: %s\n->\n%s" d (Cache_key.show cache_key)
                  (Res.show r));
            return r
        | _ ->
            info (fun m ->
                m "[Level %d] === Var (%a) ===" d Interp.Pp.pp_expr expr);
            let cycle_label = (expr, sigma) in
            let est = V_key.Estate (expr, sigma, sid) in
            if Set.mem v est then (
              (* Var Stub *)
              debug (fun m -> m "Stubbed");
              info (fun m ->
                  m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr expr);
              cache cache_key [ EStubAtom cycle_label ])
            else (
              debug (fun m -> m "Didn't stub");
              match get_myfun l with
              | Some (Fun (Ident x1, _, l_myfun)) ->
                  if String.(x = x1) then (
                    (* Var Local *)
                    info (fun m ->
                        m "[Level %d] === Var Local (%a) ===" d
                          Interp.Pp.pp_expr expr);
                    debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                    let s_hd, s_tl = (List.hd_exn sigma, List.tl_exn sigma) in
                    match get_myexpr s_hd with
                    | App (_, e2, l') ->
                        debug (fun m -> m "Begin stitching stacks");
                        debug (fun m ->
                            m "Head of candidate fragments must be: %d" l');
                        debug (fun m ->
                            m "Tail of candidate fragments must start with: %a"
                              Sigma.pp s_tl);
                        (* enumerate all matching stacks in the set *)
                        debug (fun m -> m "S: %a" S.pp s);
                        let sufs = suffixes l' s_tl s in
                        let%bind r1 =
                          List.fold sufs ~init:(return empty_res)
                            ~f:(fun acc suf ->
                              debug (fun m ->
                                  m
                                    "[Level %d] Stitched! Evaluating App \
                                     argument, using stitched stack %a"
                                    d Sigma.pp suf);
                              (* stitch the stack to gain more precision *)
                              let%bind rs = acc in
                              let%bind r0 =
                                local d
                                  (fun ({ v; _ } as env) ->
                                    { env with v = Set.add v est })
                                  (analyze_aux ~caching d e2 suf pi)
                              in
                              return (List.fold r0 ~init:rs ~f:Set.add))
                        in
                        info (fun m ->
                            m "[Level %d] *** Var Local (%a) ***" d
                              Interp.Pp.pp_expr expr);
                        info (fun m ->
                            m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr
                              expr);
                        let r1 = Set.elements r1 in
                        let r1 = elim_stub r1 (St.Estate cycle_label) in
                        cache cache_key [ EResAtom (r1, cycle_label) ]
                    | _ -> raise Unreachable)
                  else (
                    (* Var Non-Local *)
                    info (fun m ->
                        m "[Level %d] === Var Non-Local (%a) ===" d
                          Interp.Pp.pp_expr expr);
                    debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                    debug (fun m -> m "Reading App at front of sigma");
                    match get_myexpr (List.hd_exn sigma) with
                    | App (e1, _, l2) ->
                        debug (fun m ->
                            m "Fun being applied at front of sigma: %a"
                              Interp.Pp.pp_expr e1);
                        let e1st = V_key.Estate (e1, sigma, sid) in
                        if Set.mem v e1st then (
                          debug (fun m -> m "[Var Non-Local] Stubbed e1");
                          info (fun m ->
                              m "[Level %d] *** Var Non-Local (%a) ***" d
                                Interp.Pp.pp_expr expr);
                          info (fun m ->
                              m "[Level %d] *** Var (%s, %d) ***" d x l);
                          cache cache_key [ EStubAtom (e1, sigma) ])
                        else
                          let sigma_tl = List.tl_exn sigma in
                          debug (fun m -> m "Begin stitching stacks");
                          debug (fun m -> m "S: %a" S.pp s);
                          let sufs = suffixes l2 sigma_tl s in
                          (* enumerate all matching stacks in the set *)
                          let%bind r1 =
                            List.fold sufs ~init:(return empty_res)
                              ~f:(fun acc suf ->
                                debug (fun m ->
                                    m
                                      "[Level %d][Var Non-Local] Stitched! \
                                       Evaluating %a, using stitched stack %a"
                                      d Interp.Pp.pp_expr e1 Sigma.pp suf);
                                let%bind rs = acc in
                                let%bind r0 =
                                  local d
                                    (fun ({ v; _ } as env) ->
                                      { env with v = Set.add v e1st })
                                    (analyze_aux ~caching d e1 suf pi)
                                in
                                debug (fun m ->
                                    m "[Var Non-Local] r0: %a" Res.pp r0);
                                return (List.fold r0 ~init:rs ~f:Set.add))
                          in
                          let r1 = Set.elements r1 in
                          let r1 = simplify r1 in
                          debug (fun m ->
                              m
                                "[Level %d] Found all stitched stacks and \
                                 evaluated e1, begin relabeling variables"
                                d);
                          let%bind r2 =
                            fold_res_var ~init:(return empty_res) expr sigma d
                              r1 ~f:(fun acc x1' l1 sigma1 ->
                                if Stdlib.(x1 = x1') && l_myfun = l1 then (
                                  debug (fun m ->
                                      m
                                        "[Var Non-Local] Relabel %s with label \
                                         %d and evaluate"
                                        x l1);
                                  let%bind rs = acc in
                                  let%bind r0' =
                                    local d
                                      (fun ({ v; _ } as env) ->
                                        { env with v = Set.add v est })
                                      (analyze_aux ~caching d
                                         (Var (Ident x, l1))
                                         sigma1 pi)
                                  in
                                  return (List.fold r0' ~init:rs ~f:Set.add))
                                else acc)
                          in
                          info (fun m ->
                              m "[Level %d] *** Var Non-Local (%a) ***" d
                                Interp.Pp.pp_expr expr);
                          info (fun m ->
                              m "[Level %d] *** Var (%a) ***" d
                                Interp.Pp.pp_expr expr);
                          let r2 = Set.elements r2 in
                          let r2 = elim_stub r2 (St.Estate cycle_label) in
                          (* let r2 = [ EResAtom (r2, stub_key) ] in *)
                          cache cache_key r2
                    | _ -> raise Unreachable)
              | _ -> raise Unreachable))
    | If (e, e_true, e_false) -> (
        (* let r_true, s_true = analyze_aux ~caching d e_true sigma None s v in
           info (fun m -> m "Evaluating: %a" Interpreter.Pp.pp_expr e_false);
           let r_false, s_false = analyze_aux ~caching d e_false sigma None s v in
           (r_true @ r_false, Set.union s (Set.union s_true s_false)) *)
        info (fun m -> m "[Level %d] === If ===" d);
        let%bind r_cond = analyze_aux ~caching d e sigma pi in
        debug (fun m -> m "r_cond: %a" Res.pp r_cond);
        debug (fun m -> m "v_set:");
        log_v_set v;
        let true_sat = solve_cond r_cond true in
        let pc_true = (r_cond, true) in
        let false_sat = solve_cond r_cond false in
        let pc_false = (r_cond, false) in
        match (true_sat, false_sat) with
        | true, false ->
            info (fun m -> m "[Level %d] === If True only ===" d);
            debug (fun m -> m "Evaluating: %a" Interp.Pp.pp_expr e_true);
            let%bind r_true =
              analyze_aux ~caching d e_true sigma (Some pc_true)
            in
            info (fun m -> m "[Level %d] *** If True only ***" d);
            debug (fun m -> m "[Level %d] *** If ***" d);
            return [ PathCondAtom (pc_true, r_true) ]
        | false, true ->
            info (fun m -> m "[Level %d] === If False only ===" d);
            debug (fun m -> m "Evaluating: %a" Interp.Pp.pp_expr e_false);
            let%bind r_false =
              analyze_aux ~caching d e_false sigma (Some pc_false)
            in
            info (fun m -> m "[Level %d] *** If False only ***" d);
            info (fun m -> m "[Level %d] *** If ***" d);
            return [ PathCondAtom (pc_false, r_false) ]
        | _ ->
            info (fun m -> m "[Level %d] === If both  ===" d);
            info (fun m -> m "[Level %d] === If True ===" d);
            debug (fun m -> m "Evaluating: %a" Interp.Pp.pp_expr e_true);
            let%bind r_true =
              analyze_aux ~caching d e_true sigma (Some pc_true)
            in
            info (fun m -> m "[Level %d] *** If True ***" d);
            info (fun m -> m "[Level %d] === If False ===" d);
            debug (fun m -> m "Evaluating: %a" Interp.Pp.pp_expr e_false);
            let%bind r_false =
              analyze_aux ~caching d e_false sigma (Some pc_false)
            in
            info (fun m -> m "[Level %d] *** If False ***" d);
            info (fun m -> m "[Level %d] *** If both  ***" d);
            info (fun m -> m "[Level %d] *** If ***" d);
            let pc_false = PathCondAtom (pc_false, r_false) in
            let pc_true = PathCondAtom (pc_true, r_true) in
            return [ pc_true; pc_false ])
    | Plus (e1, e2)
    | Minus (e1, e2)
    | Mult (e1, e2)
    | Eq (e1, e2)
    | And (e1, e2)
    | Or (e1, e2)
    | Ge (e1, e2)
    | Gt (e1, e2)
    | Le (e1, e2)
    | Lt (e1, e2) ->
        info (fun m ->
            m "[Level %d] === Binop (%a) ===" d Interp.Pp.pp_expr expr);
        let%bind r1 = analyze_aux ~caching d e1 sigma pi in
        let%bind r2 = analyze_aux ~caching d e2 sigma pi in
        debug (fun m ->
            m "[Level %d] Evaluated binop to (%a <op> %a)" d Res.pp r1 Res.pp r2);
        info (fun m ->
            m "[Level %d] *** Binop (%a) ***" d Interp.Pp.pp_expr expr);
        return
          [
            (match expr with
            | Plus _ -> PlusAtom (r1, r2)
            | Minus _ -> MinusAtom (r1, r2)
            | Mult _ -> MultAtom (r1, r2)
            | Eq _ -> EqAtom (r1, r2)
            | And _ -> AndAtom (r1, r2)
            | Or _ -> OrAtom (r1, r2)
            | Ge _ -> GeAtom (r1, r2)
            | Gt _ -> GtAtom (r1, r2)
            | Le _ -> LeAtom (r1, r2)
            | Lt _ -> LtAtom (r1, r2)
            | _ -> raise Unreachable);
          ]
    | Not e ->
        let%bind r = analyze_aux ~caching d e sigma pi in
        return [ NotAtom r ]
    | Rec es ->
        es
        |> List.fold ~init:(return []) ~f:(fun acc (id, ei) ->
               let%bind rs = acc in
               let%bind r = analyze_aux ~caching d ei sigma pi in
               return ((id, r) :: rs))
        |> fun rs ->
        let%bind rs = rs in
        return [ RecAtom (List.rev rs) ]
    | Proj (e, x) ->
        let%bind r0 = analyze_aux ~caching d e sigma pi in
        return [ ProjAtom (r0, x) ]
    | Insp (x, e) ->
        let%bind r0 = analyze_aux ~caching d e sigma pi in
        return [ InspAtom (x, r0) ]
    | LetAssert (id, e1, e2) ->
        let%bind r1 = analyze_aux ~caching d e1 sigma pi in
        let r2 = eval_assert e2 id in
        return [ AssertAtom (id, r1, r2) ]
    | Let _ -> raise Unreachable
  in
  return (simplify r)

let analyze ?(verify = true) ?(caching = true) ?(graph = false) e =
  let e = trans_let None None e in
  build_myfun e None;
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  let empty_v = Set.empty (module V_key) in
  let empty_s = Set.empty (module Sigma) in

  let start_time = Stdlib.Sys.time () in
  (* TODO: make run function *)
  let r, s =
    analyze_aux ~caching 0 e [] None
      { v = empty_v; vids = Map.singleton (module V) empty_v 0 }
      {
        c = Map.empty (module Cache_key);
        s = empty_s;
        sids = Map.singleton (module S) empty_s 1;
        cnt = 2;
      }
  in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  if graph then Graph.dot_of_result r;
  debug (fun m -> m "Result: %a" Res.pp r);

  clean_up ();

  if verify then verify_result r;

  (r, runtime)
