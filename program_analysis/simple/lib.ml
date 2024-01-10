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
  let%bind { c; _ } = get () in
  let%bind () = set_cache (Map.add_exn (Map.remove c key) ~key ~data) in
  debug (fun m ->
      m "[Level %d] Add: %s\n->\n%s" d (Cache_key.show key) (Res.show data));
  return data

(** Main algorithm that performs the program analysis *)
let rec analyze_aux ?(caching = true) d expr sigma : Res.t T.t =
  let%bind { v; _ } = ask () in
  let%bind { c; s; sids; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  let%bind r =
    match expr with
    (* Value rule *)
    | Int i -> return (single_res IntAnyAtom)
    | Bool b -> return (single_res (BoolAtom b))
    (* Value Fun rule *)
    | Fun (_, _, l) -> return (single_res (FunAtom (expr, l, sigma)))
    (* Application rule *)
    | App (e, _, l) -> (
        let cache_key = Cache_key.Lkey (l, sigma, vid, sid) in
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
              cache d cache_key (single_res (LStubAtom cycle_label)))
            else (
              debug (fun m -> m "Didn't stub");
              debug (fun m -> m "sigma: %a" Sigma.pp sigma);
              let sigma' = l :: sigma in
              let pruned_sigma' = prune_sigma sigma' in
              debug (fun m -> m "sigma_pruned': %a" Sigma.pp pruned_sigma');
              debug (fun m ->
                  m "Evaluating function being applied: %a" Interp.Pp.pp_expr e);
              let%bind r1 = analyze_aux ~caching d e sigma in
              debug (fun m -> m "[App] r1 length: %d" (Set.length r1));
              let%bind { s = s1; _ } = get () in
              let v_state_s = Set.add s1 pruned_sigma' in
              let%bind () = set_s v_state_s in
              let%bind v_state_sid = get_sid v_state_s in
              let v_new = V_key.Lstate (l, sigma, v_state_sid) in
              let%bind r2 =
                Set.fold r1 ~init:(return empty_res) ~f:(fun acc a ->
                    debug (fun m ->
                        m
                          "[Level %d] [App] Evaluating 1 possible function \
                           being applied:"
                          d);
                    debug (fun m -> m "%a" Atom.pp a);
                    match a with
                    | FunAtom (Fun (_, e1, _), _, _) ->
                        debug (fun m ->
                            m
                              "[App] Evaluating body of function being \
                               applied: %a"
                              Interp.Pp.pp_expr e1);
                        let%bind rs = acc in
                        let%bind r0 =
                          local d
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v v_new })
                            (analyze_aux ~caching d e1 pruned_sigma')
                        in
                        return (Set.union rs r0)
                    | _ -> acc)
              in
              let r2 = elim_stub r2 (St.Lstate cycle_label) in
              debug (fun m -> m "[App] r2: %a" Res.pp r2);
              info (fun m ->
                  m "[Level %d] *** App (%a, %d) ***" d Interp.Pp.pp_expr expr l);
              cache d cache_key r2))
    (* Var rules *)
    | Var (Ident x, l) -> (
        let cache_key = Cache_key.Ekey (expr, sigma, vid, sid) in
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
              cache d cache_key (single_res (EStubAtom cycle_label)))
            else (
              debug (fun m -> m "Didn't stub");
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
                                     argument, using stitched stack %a:"
                                    d pp_sigma suf);
                              debug (fun m -> m "%a" Interp.Pp.pp_expr e2);
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
                            m "[Level %d] *** Var Local (%a) ***" d
                              Interp.Pp.pp_expr expr);
                        let r1 = elim_stub r1 (St.Estate cycle_label) in
                        debug (fun m -> m "[Var Local] r1: %a" Res.pp r1);
                        info (fun m ->
                            m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr
                              expr);
                        cache d cache_key r1
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
                                  (analyze_aux ~caching d e1 suf)
                              in
                              debug (fun m ->
                                  m "[Var Non-Local] r0: %a" Res.pp r0);
                              return (Set.union rs r0))
                        in
                        let r1 = simplify r1 in
                        debug (fun m -> m "r1 length: %d" (Set.length r1));
                        debug (fun m ->
                            m
                              "[Level %d] Found all stitched stacks and \
                               evaluated e1, begin relabeling variables"
                              d);
                        let%bind r2 =
                          Set.fold r1 ~init:(return empty_res) ~f:(fun acc a ->
                              debug (fun m ->
                                  m
                                    "[Level %d] Visiting 1 possible function \
                                     for e1:"
                                    d);
                              debug (fun m -> m "%a" Atom.pp a);
                              match a with
                              | FunAtom (Fun (Ident x1', _, l1), _, sigma1) ->
                                  if Stdlib.(x1 = x1') && l_myfun = l1 then (
                                    debug (fun m ->
                                        m
                                          "[Var Non-Local] Relabel %s with \
                                           label %d and evaluate"
                                          x l1);
                                    let%bind rs = acc in
                                    let%bind r0' =
                                      local d
                                        (fun ({ v; _ } as env) ->
                                          { env with v = Set.add v est })
                                        (analyze_aux ~caching d
                                           (Var (Ident x, l1))
                                           sigma1)
                                    in
                                    return (Set.union rs r0'))
                                  else acc
                              | _ -> acc)
                        in
                        info (fun m ->
                            m "[Level %d] *** Var Non-Local (%a) ***" d
                              Interp.Pp.pp_expr expr);
                        info (fun m ->
                            m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr
                              expr);
                        let r2 = elim_stub r2 (St.Estate cycle_label) in
                        debug (fun m -> m "[Var Non-Local] r2: %a" Res.pp r2);
                        cache d cache_key r2
                    | _ -> raise Unreachable)
              | _ -> raise Unreachable))
    (* Conditional rule *)
    | If (e, e_true, e_false) -> (
        debug (fun m -> m "[Level %d] === If ===" d);
        let%bind r_cond = analyze_aux ~caching d e sigma in
        match Set.elements r_cond with
        (* Precise only when if condition is a simple boolean *)
        | [ BoolAtom b ] ->
            debug (fun m -> m "[Level %d] === If %b ===" d b);
            if b then (
              let%bind r_true = analyze_aux ~caching d e_true sigma in
              debug (fun m -> m "[Level %d] *** If %b ***" d b);
              return r_true)
            else
              let%bind r_false = analyze_aux ~caching d e_false sigma in
              debug (fun m -> m "[Level %d] *** If %b ***" d b);
              return r_false
        (* Otherwise, analyze both branches *)
        | _ ->
            debug (fun m -> m "[Level %d] === If Both ===" d);
            let%bind r_true = analyze_aux ~caching d e_true sigma in
            let%bind r_false = analyze_aux ~caching d e_false sigma in
            debug (fun m -> m "[Level %d] *** If Both ***" d);
            return (Set.union r_true r_false))
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
        let%bind r1 = analyze_aux ~caching d e1 sigma in
        let%bind r2 = analyze_aux ~caching d e2 sigma in
        debug (fun m ->
            m "[Level %d] Evaluated binop to (%a <op> %a)" d Res.pp r1 Res.pp r2);
        info (fun m ->
            m "[Level %d] *** Binop (%a) ***" d Interp.Pp.pp_expr expr);
        return
          (match expr with
          | Plus _ -> all_combs_int r1 r2 ( + )
          | Minus _ -> all_combs_int r1 r2 ( - )
          | Mult _ -> all_combs_int r1 r2 ( * )
          | And _ -> all_combs_bool r1 r2 ( && )
          | Or _ -> all_combs_bool r1 r2 ( || )
          | Eq _ -> all_combs_bool' r1 r2 ( = )
          | Ge _ -> all_combs_bool' r1 r2 ( >= )
          | Gt _ -> all_combs_bool' r1 r2 ( > )
          | Le _ -> all_combs_bool' r1 r2 ( <= )
          | Lt _ -> all_combs_bool' r1 r2 ( < )
          | _ -> raise Unreachable)
    | Not e ->
        let%bind r = analyze_aux ~caching d e sigma in
        return
          (match Set.elements r with
          | [] -> empty_res
          (* Only performs basic simplications *)
          | [ BoolAtom b ] -> single_res (BoolAtom (not b))
          | _ -> bool_tf_res)
    (* Record Value rule *)
    | Rec es ->
        es
        |> List.fold ~init:(return []) ~f:(fun acc (id, ei) ->
               let%bind rs = acc in
               let%bind r = analyze_aux ~caching d ei sigma in
               return ((id, r) :: rs))
        |> fun rs ->
        let%bind rs = rs in
        rs |> List.rev |> RecAtom |> single_res |> return
    (* Record Project rule *)
    | Proj (e, (Ident x as id)) ->
        debug (fun m -> m "[Level %d] === Proj ===" d);
        let%bind r0 = analyze_aux ~caching d e sigma in
        debug (fun m -> m "[Level %d][Proj] r0: %a.%s" d Res.pp r0 x);
        debug (fun m -> m "[Level %d] *** Proj ***" d);
        return (single_res (ProjAtom (r0, id)))
    (* Record Inspect rule *)
    | Insp ((Ident x as id), e) ->
        debug (fun m -> m "[Level %d] === Insp ===" d);
        let%bind r0 = analyze_aux ~caching d e sigma in
        debug (fun m -> m "[Level %d][Insp] r0: %s in %a" d x Res.pp r0);
        debug (fun m -> m "[Level %d] *** Insp ***" d);
        return (single_res (InspAtom (id, r0)))
    | LetAssert (id, e1, e2) -> analyze_aux ~caching d e1 sigma
    | Let _ -> raise Unreachable
  in
  return (simplify r)

(* Simple analysis entrypoint *)
let analyze ?(caching = true) e =
  let e = subst_let None None e in
  build_myfun e None;
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  let start_time = Stdlib.Sys.time () in
  let r, { sids; _ } = run (analyze_aux ~caching 0 e []) in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  debug (fun m -> m "Result: %a" Res.pp r);

  clean_up ();

  (r, runtime)
