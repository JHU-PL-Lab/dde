(** Core algorithm of full program analysis per paper Section 4.3 *)

open Core
open Logs
open Interp.Ast
open Res_fv
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
  (* Guiding assertion: forall r, P(¬b) => false *)
  let guide = (p <-- [ zbool (not b) ]) --> zfalse in

  (* Alternative (equivalent) guiding assertion:
     forall r, P(r) => r = b *)
  (* let rb = zconst "r" bsort in
     let guide = [ rb ] |. (p <-- [ rb ]) --> (rb === zbool b) in *)
  Z3.Solver.add solver (guide :: chcs);

  match Z3.Solver.check solver [] with
  (* If sat, then if condition must be `b` *)
  | SATISFIABLE -> true
  (* Otherwise, if condition cannot only be `b` *)
  | UNSATISFIABLE | UNKNOWN -> false

let rec eval_assert_aux e =
  match e with
  | Expr.Int i -> IntResFv i
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
      Format.printf "%a\n" Expr.pp e;
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
  | Expr.Bool b -> BoolResFv b
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
      | Proj (e1, x) -> raise (Runtime_error "Not supported")
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
let rec fold_res_app ~init ~f d =
  List.fold ~init ~f:(fun acc a ->
      match a with
      | FunAtom (Fun (_, e1, _), _) ->
          debug (fun m ->
              m "[Level %d] [App] Evaluate a possible applied function: %a" d
                Atom.pp a);
          f acc e1
      | LResAtom (r, _) | EResAtom (r, _) | PathCondAtom (_, r) ->
          fold_res_app ~init:acc ~f d r
      | LStubAtom _ | EStubAtom _ -> acc
      | _ -> raise Unreachable)

(** Helper to recursively visit function disjuncts for the Var Non-Local rule *)
let rec fold_res_var ~init ~f d expr =
  List.fold ~init ~f:(fun acc a ->
      match a with
      | FunAtom (Fun (_, _, sv), sigma1)
      (* Check if the current var can be looked up from the
         context of this function *)
        when List.mem sv expr ~equal:Expr.( = ) ->
          debug (fun m ->
              m "[Level %d] Visit a possible e1 function:\n%a" d Atom.pp a);
          f acc sigma1
      | LResAtom (r, _) | EResAtom (r, _) | PathCondAtom (_, r) ->
          fold_res_var ~init:acc ~f d expr r
      | FunAtom _ ->
          debug (fun m -> m "Not a match");
          acc
      | LStubAtom _ | EStubAtom _ -> acc
      | _ -> raise Unreachable)

open ReaderState
open ReaderState.Let_syntax

(** Caches the analysis result *)
let cache d key data =
  let%bind () =
    set_cache (fun c -> Map.add_exn (Map.remove c key) ~key ~data)
  in
  debug (fun m ->
      m "[Level %d] Cache add: %s\n->\n%s" d (Cache_key.show key)
        (Res.show data));
  return data

(** Main algorithm that performs the program analysis per paper Fig. 17 *)
let rec analyze_aux ~caching d expr sigma pi : Res.t T.t =
  let%bind { v; _ } = ask () in
  let%bind { c; s; sids; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  match expr with
  (* Value rule *)
  | Expr.Int i -> return [ IntAtom i ]
  | Bool b -> return [ BoolAtom b ]
  (* Value Fun rule *)
  | Fun _ -> return [ FunAtom (expr, sigma) ]
  (* Application rule *)
  | App (e, _, l) -> (
      let cache_key = Cache_key.Lkey (l, sigma, vid, sid, pi) in
      match Map.find c cache_key with
      | Some r when caching ->
          debug (fun m ->
              m "[Level %d] Cache hit: %s\n->\n%s" d (Cache_key.show cache_key)
                (Res.show r));
          return r
      | _ ->
          info (fun m -> m "[Level %d] === App (%a, %d) ===" d Expr.pp expr l);
          let cycle_label = (l, sigma) in
          let v_state = V_key.Lstate (l, sigma, sid) in
          if Set.mem v v_state then (
            (* App Stub rule *)
            (* If we've analyzed the exact same program state, stub *)
            debug (fun m -> m "Stubbed");
            info (fun m -> m "[Level %d] *** App (%a, %d) ***" d Expr.pp expr l);
            cache d cache_key [ LStubAtom cycle_label ])
          else (
            debug (fun m -> m "Didn't stub");
            debug (fun m -> m "sigma: %a" Sigma.pp sigma);
            let pruned_sigma = prune_sigma (l :: sigma) in
            debug (fun m -> m "pruned_sigma: %a" Sigma.pp pruned_sigma);
            debug (fun m -> m "Evaluate applied function: %a" Expr.pp e);
            let%bind r1 = analyze_aux ~caching d e sigma pi in
            debug (fun m -> m "[App] r1 length: %d" (List.length r1));
            let%bind { s = s1; _ } = get () in
            let v_state_s = Set.add s1 pruned_sigma in
            let%bind () = set_s v_state_s in
            let%bind v_state_sid = get_sid v_state_s in
            let v_new = V_key.Lstate (l, sigma, v_state_sid) in
            let%bind r2 =
              fold_res_app d r1 ~init:(return []) ~f:(fun acc e1 ->
                  debug (fun m ->
                      m "[App] Evaluate body of applied function: %a" Expr.pp e1);
                  let%bind rs = acc in
                  let%bind r0 =
                    local d
                      (fun ({ v; _ } as env) ->
                        { env with v = Set.add v v_new })
                      (analyze_aux ~caching d e1 pruned_sigma pi)
                  in
                  return (rs @ r0))
            in
            let r2 = r2 |> simpl_res |> elim_stub (St.Lstate cycle_label) in
            debug (fun m -> m "[App] r2: %a" Res.pp r2);
            info (fun m -> m "[Level %d] *** App (%a, %d) ***" d Expr.pp expr l);
            cache d cache_key [ LResAtom (r2, cycle_label) ]))
  (* Var rules *)
  | Var (id, idx) -> (
      let cache_key = Cache_key.Ekey (expr, sigma, vid, sid, pi) in
      match Map.find c cache_key with
      | Some r when caching ->
          debug (fun m ->
              m "[Level %d] Cache hit: %s\n->\n%s" d (Cache_key.show cache_key)
                (Res.show r));
          return r
      | _ ->
          info (fun m -> m "[Level %d] === Var (%a) ===" d Expr.pp expr);
          let cycle_label = (expr, sigma) in
          let est = V_key.Estate (expr, sigma, sid) in
          if Set.mem v est then (
            (* Var Stub rule *)
            debug (fun m -> m "Stubbed");
            info (fun m -> m "[Level %d] *** Var (%a) ***" d Expr.pp expr);
            cache d cache_key [ EStubAtom cycle_label ])
          else (
            debug (fun m -> m "Didn't stub");
            let s_hd, s_tl = (List.hd_exn sigma, List.tl_exn sigma) in
            match get_myexpr s_hd with
            | App (e1, e2, l) ->
                if idx = 0 then (
                  (* Var Local rule *)
                  info (fun m ->
                      m "[Level %d] === Var Local (%a) ===" d Expr.pp expr);
                  debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                  debug (fun m -> m "Begin stitching stacks");
                  debug (fun m -> m "S: %a" S.pp s);
                  (* Stitch the stack to gain more precision *)
                  let sufs = suffixes l s_tl s in
                  let%bind r1 =
                    List.fold sufs ~init:(return []) ~f:(fun acc suf ->
                        debug (fun m ->
                            m
                              "[Level %d] Stitched! Use stitched stack %a to \
                               evaluate App argument %a"
                              d Sigma.pp suf Expr.pp e2);
                        let%bind rs = acc in
                        let%bind r0 =
                          local d
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v est })
                            (analyze_aux ~caching d e2 suf pi)
                        in
                        return (rs @ r0))
                  in
                  info (fun m ->
                      m "[Level %d] *** Var Local (%a) ***" d Expr.pp expr);
                  let r1 =
                    r1 |> simpl_res |> elim_stub (St.Estate cycle_label)
                  in
                  debug (fun m -> m "[Var Local] r1: %a" Res.pp r1);
                  info (fun m -> m "[Level %d] *** Var (%a) ***" d Expr.pp expr);
                  cache d cache_key [ EResAtom (r1, cycle_label) ])
                else (
                  (* Var Non-Local rule *)
                  info (fun m ->
                      m "[Level %d] === Var Non-Local (%a) ===" d Expr.pp expr);
                  debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                  debug (fun m ->
                      m "Fun applied at front of sigma: %a" Expr.pp e1);
                  debug (fun m -> m "Begin stitching stacks");
                  debug (fun m -> m "S: %a" S.pp s);
                  (* Stitch the stack to gain more precision *)
                  let sufs = suffixes l s_tl s in
                  let%bind r1 =
                    List.fold sufs ~init:(return []) ~f:(fun acc suf ->
                        debug (fun m ->
                            m
                              "[Level %d][Var Non-Local] Stitched! Use \
                               stitched stack %a to evaluate %a"
                              d Sigma.pp suf Expr.pp e1);
                        let%bind rs = acc in
                        let%bind r0 =
                          local d
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v est })
                            (analyze_aux ~caching d e1 suf pi)
                        in
                        debug (fun m -> m "[Var Non-Local] r0: %a" Res.pp r0);
                        return (rs @ r0))
                  in
                  let r1 = simpl_res r1 in
                  debug (fun m ->
                      m "[Var Non-Local] r1 length: %d" (List.length r1));
                  debug (fun m ->
                      m
                        "[Level %d] Found all stitched stacks and evaluated \
                         e1, begin decrementing variables"
                        d);
                  let%bind { s = s1; _ } = get () in
                  let%bind s1id = get_sid s1 in
                  let est = V_key.Estate (expr, sigma, s1id) in
                  let%bind r2 =
                    fold_res_var d expr r1 ~init:(return [])
                      ~f:(fun acc sigma1 ->
                        let idx' = idx - 1 in
                        debug (fun m ->
                            m
                              "[Var Non-Local] Decrement %a's index to %d and \
                               evaluate it with stack %a"
                              Ident.pp id idx' Sigma.pp sigma1);
                        let%bind rs = acc in
                        let%bind r0' =
                          local d
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v est })
                            (analyze_aux ~caching d (Var (id, idx')) sigma1 pi)
                        in
                        return (rs @ r0'))
                  in
                  info (fun m ->
                      m "[Level %d] *** Var Non-Local (%a) ***" d Expr.pp expr);
                  info (fun m -> m "[Level %d] *** Var (%a) ***" d Expr.pp expr);
                  let r2 =
                    r2 |> simpl_res |> elim_stub (St.Estate cycle_label)
                  in
                  debug (fun m -> m "[Var Non-Local] r2: %a" Res.pp r2);
                  cache d cache_key r2)
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
          debug (fun m -> m "Analyze: %a" Expr.pp e_true);
          let%bind r_true =
            analyze_aux ~caching d e_true sigma (Some pc_true)
          in
          info (fun m -> m "[Level %d] *** If True only ***" d);
          debug (fun m -> m "[Level %d] *** If ***" d);
          return [ PathCondAtom (pc_true, r_true) ]
      | false, true ->
          info (fun m -> m "[Level %d] === If False only ===" d);
          debug (fun m -> m "Analyze: %a" Expr.pp e_false);
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
          debug (fun m -> m "Analyze: %a" Expr.pp e_true);
          let%bind r_true =
            analyze_aux ~caching d e_true sigma (Some pc_true)
          in
          info (fun m -> m "[Level %d] *** If True ***" d);
          info (fun m -> m "[Level %d] === If False ===" d);
          debug (fun m -> m "Analyze: %a" Expr.pp e_false);
          let%bind r_false =
            analyze_aux ~caching d e_false sigma (Some pc_false)
          in
          info (fun m -> m "[Level %d] *** If False ***" d);
          info (fun m -> m "[Level %d] *** If both  ***" d);
          info (fun m -> m "[Level %d] *** If ***" d);
          let pc_false = PathCondAtom (pc_false, r_false) in
          let pc_true = PathCondAtom (pc_true, r_true) in
          [ pc_true; pc_false ] |> simpl_res |> return)
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
      info (fun m -> m "[Level %d] === Binop (%a) ===" d Expr.pp expr);
      let%bind r1 = analyze_aux ~caching d e1 sigma pi in
      let%bind r2 = analyze_aux ~caching d e2 sigma pi in
      debug (fun m ->
          m "[Level %d] Evaluated binop to (%a <op> %a)" d Res.pp r1 Res.pp r2);
      info (fun m -> m "[Level %d] *** Binop (%a) ***" d Expr.pp expr);
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
      |> simpl_res |> return
  | Not e ->
      let%bind r = analyze_aux ~caching d e sigma pi in
      [ NotAtom r ] |> simpl_res |> return
  (* Record Value rule *)
  | Rec es ->
      es
      |> List.fold ~init:(return []) ~f:(fun acc (id, ei) ->
             let%bind rs = acc in
             let%bind r = analyze_aux ~caching d ei sigma pi in
             return ((id, r) :: rs))
      |> fun rs ->
      let%bind rs = rs in
      rs |> List.rev |> RecAtom |> Fn.flip List.cons [] |> return
  (* Record Project rule *)
  | Proj (e, x) ->
      let%bind r0 = analyze_aux ~caching d e sigma pi in
      [ ProjAtom (r0, x) ] |> simpl_res |> return
  (* Record Inspect rule *)
  | Insp (x, e) ->
      let%bind r0 = analyze_aux ~caching d e sigma pi in
      [ InspAtom (x, r0) ] |> simpl_res |> return
  (* e.g., letassert x = 10 in x >= 0 *)
  | LetAssert (id, e1, e2) ->
      let%bind r1 = analyze_aux ~caching d e1 sigma pi in
      let r2 = eval_assert e2 id in
      return [ AssertAtom (id, r1, r2) ]
  | Let _ -> raise Unreachable

(* Full analysis entry point *)
let analyze ?(verify = true) ?(caching = true) ?(graph = false) ?(name = "test")
    e =
  let e = e |> subst_let None None |> assign_index |> scope_vars in
  debug (fun m -> m "%a" Expr.pp e);

  (* debug (fun m -> m "%a" Expr.pp e); *)
  let start_time = Stdlib.Sys.time () in
  let r, s = run (analyze_aux ~caching 0 e [] None) in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  if graph then Graph.dot_of_result r name;
  debug (fun m -> m "Result: %a" Res.pp r);

  clean_up ();

  if verify then verify_result r;

  (r, runtime)
