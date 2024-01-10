(** Core algorithm of full program analysis per paper Section 4.3 *)

open Core
open Logs
open Interp.Ast
open Utils
open Utils.Atom
open Utils
open Solver
open Simplifier
open Exns

(** Determines whether a conditional branch is feasible using Z3 *)
let solve_cond r b =
  let solver = Z3.Solver.mk_solver_s ctx "HORN" in
  let (), { chcs; entry_decl; _ } = State.run (Solver.chcs_of_res r) in
  let chcs = Set.elements chcs in
  let p = Option.value_exn entry_decl in
  let rb = zconst "r" bsort in
  (* Guiding assertion: forall r, P(r) => r = `b`  *)
  let manual = [ rb ] |. (p <-- [ rb ]) --> (rb === zbool b) in
  Z3.Solver.add solver (manual :: chcs);

  match Z3.Solver.check solver [] with
  (* If sat, then if condition must be `b` *)
  | SATISFIABLE -> true
  (* Otherwise, if condition cannot only be `b` *)
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

(** Evaluates the assertion part of letassert.
    Only allows the following forms:
    - variable-free binary operations (=, >=, >, <=, <)
    - <var>
    - not <var>
    - <var> <op> <value>
*)
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

(** Helper to recursively visit function disjuncts for the Application rule *)
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
      | _ -> raise Unreachable)

(** Helper to recursively visit function disjuncts for the Var Non-Local rule *)
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
      | _ -> raise Unreachable)

open ReaderState
open ReaderState.Let_syntax

(** Caches the analysis result *)
let cache key data =
  let%bind { c; _ } = get () in
  let%bind () = set_cache (Map.add_exn (Map.remove c key) ~key ~data) in
  debug (fun m ->
      m "[Cache] Add: %s\n->\n%s" (Cache_key.show key) (Res.show data));
  return data

(** Main algorithm that performs the program analysis per paper Fig. 17 *)
let rec analyze_aux ~caching d expr sigma pi : Res.t T.t =
  let%bind { v; _ } = ask () in
  let%bind { c; s; sids; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  let%bind r =
    match expr with
    (* Value rule *)
    | Int i -> return [ IntAtom i ]
    | Bool b -> return [ BoolAtom b ]
    (* Value Fun rule *)
    | Fun (_, _, l) -> return [ FunAtom (expr, l, sigma) ]
    (* Application rule *)
    | App (e, _, l) -> (
        let cache_key = Cache_key.Lkey (l, sigma, vid, sid, pi) in
        (* let cache_key = Cache_key.Lkey (l, sigma, sid, pi) in *)
        match Map.find c cache_key with
        | Some r when caching ->
            debug (fun m ->
                m "[Level %d] Cache hit: %s\n->\n%s" d
                  (Cache_key.show cache_key) (Res.show r));
            return r
        | _ ->
            info (fun m ->
                m "[Level %d] === App (%a, %d) ===" d Interp.Pp.pp_expr expr l);
            let cycle_label = (l, sigma) in
            let v_state = V_key.Lstate (l, sigma, sid) in
            if Set.mem v v_state then (
              (* App Stub rule *)
              (* If we've analyzed the exact same program state, stub *)
              debug (fun m -> m "Stubbed");
              info (fun m ->
                  m "[Level %d] *** App (%a, %d) ***" d Interp.Pp.pp_expr expr l);
              cache cache_key [ LStubAtom cycle_label ])
            else (
              debug (fun m -> m "Didn't stub");
              debug (fun m -> m "sigma: %a" Sigma.pp sigma);
              let sigma' = l :: sigma in
              let pruned_sigma' = prune_sigma sigma' in
              debug (fun m -> m "sigma_pruned': %a" Sigma.pp pruned_sigma');
              debug (fun m ->
                  m "Evaluating function being applied: %a" Interp.Pp.pp_expr e);
              let%bind r1 = analyze_aux ~caching d e sigma pi in
              debug (fun m -> m "[App] r1 length: %d" (List.length r1));
              let%bind { s = s1; _ } = get () in
              let v_state_s = Set.add s1 pruned_sigma' in
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
              let r2 = elim_stub (Set.elements r2) (St.Lstate cycle_label) in
              info (fun m ->
                  m "[Level %d] *** App (%a, %d) ***" d Interp.Pp.pp_expr expr l);
              cache cache_key [ LResAtom (r2, cycle_label) ]))
    (* Var rules *)
    | Var (Ident x, l) -> (
        let cache_key = Cache_key.Ekey (expr, sigma, vid, sid, pi) in
        (* let cache_key = Cache_key.Ekey (expr, sigma, sid, pi) in *)
        match Map.find c cache_key with
        | Some r when caching ->
            debug (fun m ->
                m "[Level %d] Cache hit: %s\n->\n%s" d
                  (Cache_key.show cache_key) (Res.show r));
            return r
        | _ ->
            info (fun m ->
                m "[Level %d] === Var (%a) ===" d Interp.Pp.pp_expr expr);
            let cycle_label = (expr, sigma) in
            let est = V_key.Estate (expr, sigma, sid) in
            if Set.mem v est then (
              (* Var Stub rule *)
              debug (fun m -> m "Stubbed");
              info (fun m ->
                  m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr expr);
              cache cache_key [ EStubAtom cycle_label ])
            else (
              debug (fun m -> m "Didn't stub");
              debug (fun m -> m "V key: %a" V_key.pp est);
              debug (fun m -> m "V: %a" V.pp v);
              match get_myfun l with
              | Some (Fun (Ident x1, _, l_myfun)) ->
                  if String.(x = x1) then (
                    (* Var Local rule *)
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
                        debug (fun m -> m "S: %a" S.pp s);
                        (* Stitch the stack to gain more precision *)
                        let sufs = suffixes l' s_tl s in
                        let%bind r1 =
                          List.fold sufs ~init:(return empty_res)
                            ~f:(fun acc suf ->
                              debug (fun m ->
                                  m
                                    "[Level %d] Stitched! Evaluating App \
                                     argument, using stitched stack %a"
                                    d Sigma.pp suf);
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
                        let r1 =
                          elim_stub (Set.elements r1) (St.Estate cycle_label)
                        in
                        cache cache_key [ EResAtom (r1, cycle_label) ]
                    | _ -> raise Unreachable)
                  else (
                    (* Var Non-Local rule *)
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
                        let sigma_tl = List.tl_exn sigma in
                        debug (fun m -> m "Begin stitching stacks");
                        debug (fun m -> m "S: %a" S.pp s);
                        (* Stitch the stack to gain more precision *)
                        let sufs = suffixes l2 sigma_tl s in
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
                                    { env with v = Set.add v est })
                                  (analyze_aux ~caching d e1 suf pi)
                              in
                              debug (fun m ->
                                  m "[Var Non-Local] r0: %a" Res.pp r0);
                              return (List.fold r0 ~init:rs ~f:Set.add))
                        in
                        let r1 = r1 |> Set.elements |> simplify in
                        debug (fun m ->
                            m
                              "[Level %d] Found all stitched stacks and \
                               evaluated e1, begin relabeling variables"
                              d);
                        let%bind r2 =
                          fold_res_var ~init:(return empty_res) expr sigma d r1
                            ~f:(fun acc x1' l1 sigma1 ->
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
                            m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr
                              expr);
                        let r2 =
                          elim_stub (Set.elements r2) (St.Estate cycle_label)
                        in
                        cache cache_key r2
                    | _ -> raise Unreachable)
              | _ -> raise Unreachable))
    (* Conditional rule *)
    | If (e, e_true, e_false) -> (
        info (fun m -> m "[Level %d] === If ===" d);
        let%bind r_cond = analyze_aux ~caching d e sigma pi in
        debug (fun m -> m "r_cond: %a" Res.pp r_cond);
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
            (* In particular, if both `true_sat` and `false_sat` are false,
               then both branches are feasible and should be analyzed *)
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
    (* Operation rule *)
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
    (* Record Value rule *)
    | Rec es ->
        es
        |> List.fold ~init:(return []) ~f:(fun acc (id, ei) ->
               let%bind rs = acc in
               let%bind r = analyze_aux ~caching d ei sigma pi in
               return ((id, r) :: rs))
        |> fun rs ->
        let%bind rs = rs in
        return [ RecAtom (List.rev rs) ]
    (* Record Project rule *)
    | Proj (e, x) ->
        let%bind r0 = analyze_aux ~caching d e sigma pi in
        return [ ProjAtom (r0, x) ]
    (* Record Inspect rule *)
    | Insp (x, e) ->
        let%bind r0 = analyze_aux ~caching d e sigma pi in
        return [ InspAtom (x, r0) ]
    (* e.g., letassert x = 10 in x >= 0 *)
    | LetAssert (id, e1, e2) ->
        let%bind r1 = analyze_aux ~caching d e1 sigma pi in
        let r2 = eval_assert e2 id in
        return [ AssertAtom (id, r1, r2) ]
    | Let _ -> raise Unreachable
  in
  return (simplify r)

(* Full analysis entrypoint *)
let analyze ?(verify = true) ?(caching = true) ?(graph = false) ?(name = "test")
    e =
  let e = subst_let None None e in
  build_myfun e None;
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  let start_time = Stdlib.Sys.time () in
  let r, s = run (analyze_aux ~caching 0 e [] None) in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  if graph then Graph.dot_of_result r name;
  debug (fun m -> m "Result: %a" Res.pp r);

  clean_up ();

  if verify then verify_result r;

  (r, runtime)
