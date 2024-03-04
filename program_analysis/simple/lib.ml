open Core
open Logs
open Interp.Ast
open Exns
open Utils
open Simplifier
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

(** Main algorithm that performs the program analysis *)
let rec analyze_aux ?(caching = true) d expr sigma : Res.t T.t =
  let%bind { v; _ } = ask () in
  let%bind { c; s; sids; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  match expr with
  (* Value rule *)
  | Expr.Int i -> return (single_res IntAnyAtom)
  | Bool b -> return (single_res (BoolAtom b))
  (* Value Fun rule *)
  | Fun _ -> return (single_res (FunAtom (expr, sigma)))
  (* Application rule *)
  | App (e, _, l) -> (
      let cache_key = Cache_key.Lkey (l, sigma, vid, sid) in
      (* let cache_key = Cache_key.Lkey (l, sigma, sid) in *)
      match Map.find c cache_key with
      | Some r when caching ->
          debug (fun m ->
              m "[Level %d] Cache hit: %s\n->\n%s" d (Cache_key.show cache_key)
                (Res.show r));
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
            cache d cache_key (single_res (LStubAtom cycle_label)))
          else (
            debug (fun m -> m "Didn't stub");
            debug (fun m -> m "sigma: %a" Sigma.pp sigma);
            let pruned_sigma = prune_sigma (l :: sigma) in
            debug (fun m -> m "pruned_sigma: %a" Sigma.pp pruned_sigma);
            debug (fun m ->
                m "Evaluate applied function: %a" Interp.Pp.pp_expr e);
            let%bind r1 = analyze_aux ~caching d e sigma in
            debug (fun m -> m "[App] r1 length: %d" (Set.length r1));
            let%bind { s = s1; _ } = get () in
            let v_state_s = Set.add s1 pruned_sigma in
            let%bind () = set_s v_state_s in
            let%bind v_state_sid = get_sid v_state_s in
            let v_new = V_key.Lstate (l, sigma, v_state_sid) in
            let%bind r2 =
              Set.fold r1 ~init:(return empty_res) ~f:(fun acc a ->
                  debug (fun m ->
                      m
                        "[Level %d] [App] Evaluate a possible applied \
                         function: %a"
                        d Atom.pp a);
                  match a with
                  | FunAtom (Fun (_, e1, _), _) ->
                      debug (fun m ->
                          m "[App] Evaluate body of applied function: %a"
                            Interp.Pp.pp_expr e1);
                      let%bind rs = acc in
                      let%bind r0 =
                        local d
                          (fun ({ v; _ } as env) ->
                            { env with v = Set.add v v_new })
                          (analyze_aux ~caching d e1 pruned_sigma)
                      in
                      return (Set.union rs r0)
                  | _ -> acc)
            in
            let r2 = simplify (elim_stub r2 (St.Lstate cycle_label)) in
            (* let r2 = elim_stub r2 (St.Lstate cycle_label) in *)
            debug (fun m -> m "[App] r2: %a" Res.pp r2);
            info (fun m ->
                m "[Level %d] *** App (%a, %d) ***" d Interp.Pp.pp_expr expr l);
            cache d cache_key r2))
  (* Var rules *)
  | Var (id, idx) -> (
      let cache_key = Cache_key.Ekey (expr, sigma, vid, sid) in
      (* let cache_key = Cache_key.Ekey (expr, sigma, sid) in *)
      match Map.find c cache_key with
      | Some r when caching ->
          debug (fun m ->
              m "[Level %d] Cache hit: %s\n->\n%s" d (Cache_key.show cache_key)
                (Res.show r));
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
            cache d cache_key (single_res (EStubAtom cycle_label)))
          else (
            debug (fun m -> m "Didn't stub");
            let s_hd, s_tl = (List.hd_exn sigma, List.tl_exn sigma) in
            match get_myexpr s_hd with
            | App (e1, e2, l) ->
                if idx = 0 then (
                  (* Var Local rule *)
                  info (fun m ->
                      m "[Level %d] === Var Local (%a) ===" d Interp.Pp.pp_expr
                        expr);
                  debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                  debug (fun m -> m "Begin stitching stacks");
                  debug (fun m -> m "S: %a" S.pp s);
                  (* Stitch the stack to gain more precision *)
                  let sufs = suffixes l s_tl s in
                  let%bind r1 =
                    List.fold sufs ~init:(return empty_res) ~f:(fun acc suf ->
                        debug (fun m ->
                            m
                              "[Level %d] Stitched! Use stitched stack %a to \
                               evaluate App argument %a"
                              d Sigma.pp suf Interp.Pp.pp_expr e2);
                        let%bind rs = acc in
                        let%bind r0 =
                          local d
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v est })
                            (analyze_aux ~caching d e2 suf)
                        in
                        return (Set.union rs r0))
                  in
                  info (fun m ->
                      m "[Level %d] *** Var Local (%a) ***" d Interp.Pp.pp_expr
                        expr);
                  let r1 = simplify (elim_stub r1 (St.Estate cycle_label)) in
                  (* let r1 = elim_stub r1 (St.Estate cycle_label) in *)
                  debug (fun m -> m "[Var Local] r1: %a" Res.pp r1);
                  info (fun m ->
                      m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr expr);
                  cache d cache_key r1)
                else (
                  (* Var Non-Local rule *)
                  info (fun m ->
                      m "[Level %d] === Var Non-Local (%a) ===" d
                        Interp.Pp.pp_expr expr);
                  debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                  debug (fun m ->
                      m "Fun applied at front of sigma: %a" Interp.Pp.pp_expr e1);
                  debug (fun m -> m "Begin stitching stacks");
                  debug (fun m -> m "S: %a" S.pp s);
                  (* Stitch the stack to gain more precision *)
                  let sufs = suffixes l s_tl s in
                  let%bind r1 =
                    List.fold sufs ~init:(return empty_res) ~f:(fun acc suf ->
                        debug (fun m ->
                            m
                              "[Level %d][Var Non-Local] Stitched! Use \
                               stitched stack %a to evaluate %a"
                              d Sigma.pp suf Interp.Pp.pp_expr e1);
                        let%bind rs = acc in
                        let%bind r0 =
                          local d
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v est })
                            (analyze_aux ~caching d e1 suf)
                        in
                        debug (fun m -> m "[Var Non-Local] r0: %a" Res.pp r0);
                        return (Set.union rs r0))
                  in
                  let r1 = simplify r1 in
                  debug (fun m ->
                      m "[Var Non-Local] r1 length: %d" (Set.length r1));
                  debug (fun m ->
                      m
                        "[Level %d] Found all stitched stacks and evaluated \
                         e1, begin decrementing variables"
                        d);
                  let%bind { s = s1; _ } = get () in
                  let%bind s1id = get_sid s1 in
                  let est = V_key.Estate (expr, sigma, s1id) in
                  let%bind r2 =
                    Set.fold r1 ~init:(return empty_res) ~f:(fun acc a ->
                        debug (fun m ->
                            m "[Level %d] Visit a possible e1 function:\n%a" d
                              Atom.pp a);
                        match a with
                        | FunAtom (Fun (_, _, sv), sigma1)
                        (* Check if the current var can be looked up from the
                           context of this function *)
                          when List.mem sv expr ~equal:(fun e1 e2 ->
                                   Expr.compare e1 e2 = 0) ->
                            let i' = idx - 1 in
                            debug (fun m ->
                                m
                                  "[Var Non-Local] Decrement %a's index to %d \
                                   and evaluate it with stack %a"
                                  Interp.Pp.pp_ident id i' Sigma.pp sigma1);
                            let%bind rs = acc in
                            let%bind r0' =
                              local d
                                (fun ({ v; _ } as env) ->
                                  { env with v = Set.add v est })
                                (analyze_aux ~caching d (Var (id, i')) sigma1)
                            in
                            return (Set.union rs r0')
                        | FunAtom (Fun (_, _, sv), _) ->
                            debug (fun m -> m "Not a match");
                            (* debug (fun m -> m "sv: %a" Scope_vars.pp sv); *)
                            acc
                        | _ -> acc)
                  in
                  info (fun m ->
                      m "[Level %d] *** Var Non-Local (%a) ***" d
                        Interp.Pp.pp_expr expr);
                  info (fun m ->
                      m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr expr);
                  let r2 = simplify (elim_stub r2 (St.Estate cycle_label)) in
                  (* let r2 = elim_stub r2 (St.Estate cycle_label) in *)
                  debug (fun m -> m "[Var Non-Local] r2: %a" Res.pp r2);
                  cache d cache_key r2)
            | _ -> raise Unreachable))
  (* Conditional rule *)
  | If (e, e_true, e_false) -> (
      info (fun m -> m "[Level %d] === If ===" d);
      let%bind r_cond = analyze_aux ~caching d e sigma in
      match Set.elements r_cond with
      (* Precise only when if condition is a simple boolean *)
      | [ BoolAtom b ] ->
          info (fun m -> m "[Level %d] === If %b ===" d b);
          if b then (
            let%bind r_true = analyze_aux ~caching d e_true sigma in
            info (fun m -> m "[Level %d] *** If %b ***" d b);
            r_true |> simplify |> return)
          else
            let%bind r_false = analyze_aux ~caching d e_false sigma in
            info (fun m -> m "[Level %d] *** If %b ***" d b);
            r_false |> simplify |> return
      (* Otherwise, analyze both branches *)
      | _ ->
          info (fun m -> m "[Level %d] === If Both ===" d);
          let%bind r_true = analyze_aux ~caching d e_true sigma in
          let%bind r_false = analyze_aux ~caching d e_false sigma in
          info (fun m -> m "[Level %d] *** If Both ***" d);
          Set.union r_true r_false |> simplify |> return)
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
      info (fun m -> m "[Level %d] === Binop (%a) ===" d Interp.Pp.pp_expr expr);
      let%bind r1 = analyze_aux ~caching d e1 sigma in
      let%bind r2 = analyze_aux ~caching d e2 sigma in
      debug (fun m ->
          m "[Level %d] Evaluated binop to (%a <op> %a)" d Res.pp r1 Res.pp r2);
      info (fun m -> m "[Level %d] *** Binop (%a) ***" d Interp.Pp.pp_expr expr);
      (match expr with
      | Plus _ -> all_combs_int r1 r2 ( + )
      | Minus _ -> all_combs_int r1 r2 ( - )
      | Mult _ -> all_combs_int r1 r2 ( * )
      | Eq _ -> all_combs_bool' r1 r2 ( = )
      | And _ -> all_combs_bool r1 r2 ( && )
      | Or _ -> all_combs_bool r1 r2 ( || )
      | Ge _ -> all_combs_bool' r1 r2 ( >= )
      | Gt _ -> all_combs_bool' r1 r2 ( > )
      | Le _ -> all_combs_bool' r1 r2 ( <= )
      | Lt _ -> all_combs_bool' r1 r2 ( < )
      | _ -> raise Unreachable)
      |> simplify |> return
  | Not e ->
      let%bind r = analyze_aux ~caching d e sigma in
      (match Set.elements r with
      | [] -> empty_res
      (* Only performs basic simplications *)
      | [ BoolAtom b ] -> single_res (BoolAtom (not b))
      | _ -> bool_tf_res)
      |> simplify |> return
  (* Record Value rule *)
  | Rec es ->
      es
      |> List.fold ~init:(return []) ~f:(fun acc (id, ei) ->
             let%bind rs = acc in
             let%bind r = analyze_aux ~caching d ei sigma in
             return ((id, r) :: rs))
      |> fun rs ->
      let%bind rs = rs in
      rs |> List.rev |> RecAtom |> single_res |> simplify |> return
  (* Record Project rule *)
  | Proj (e, (Ident x as id)) ->
      info (fun m -> m "[Level %d] === Proj ===" d);
      let%bind r0 = analyze_aux ~caching d e sigma in
      debug (fun m -> m "[Level %d][Proj] r0: %a.%s" d Res.pp r0 x);
      info (fun m -> m "[Level %d] *** Proj ***" d);
      ProjAtom (r0, id) |> single_res |> simplify |> return
  (* Record Inspect rule *)
  | Insp ((Ident x as id), e) ->
      info (fun m -> m "[Level %d] === Insp ===" d);
      let%bind r0 = analyze_aux ~caching d e sigma in
      debug (fun m -> m "[Level %d][Insp] r0: %s in %a" d x Res.pp r0);
      info (fun m -> m "[Level %d] *** Insp ***" d);
      InspAtom (id, r0) |> single_res |> simplify |> return
  | LetAssert (id, e1, e2) ->
      let%bind r1 = analyze_aux ~caching d e1 sigma in
      r1 |> simplify |> return
  | Let _ -> raise Unreachable

(* Simple analysis entry point *)
let analyze ?(caching = true) e =
  let e = e |> subst_let None None |> assign_index |> scope_vars in
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);

  let start_time = Stdlib.Sys.time () in
  let r, { sids; _ } = run (analyze_aux ~caching 0 e []) in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  debug (fun m -> m "Result: %a" Res.pp r);

  clean_up ();

  (r, runtime)
