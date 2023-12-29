open Core
open Logs
open Interp.Ast
open Exns
open Utils
open Simplifier

let rec eval_assert_aux e =
  match e with
  | Int i -> IntResFv i
  | Bool b -> BoolResFv b
  | Plus (e1, e2)
  | Minus (e1, e2)
  | Equal (e1, e2)
  | Ge (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Lt (e1, e2) -> (
      match (eval_assert_aux e1, eval_assert_aux e2) with
      | IntResFv i1, IntResFv i2 -> (
          match e with
          | Plus _ -> IntResFv (i1 + i2)
          | Minus _ -> IntResFv (i1 - i2)
          | Equal _ -> BoolResFv (i1 = i2)
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
      raise BadAssert

(** only allow the following forms:
    - arbitrary variable-free arithmetic
    - <var>
    - not <var>
    - <var> <op> <value> *)
let eval_assert e id =
  match e with
  | Bool b -> BoolResFv b
  | Var (id', _) when Stdlib.(id = id') -> VarResFv id'
  | Equal (e1, e2) | Ge (e1, e2) | Gt (e1, e2) | Le (e1, e2) | Lt (e1, e2) -> (
      match e1 with
      | Var (id', _) when Stdlib.(id = id') -> (
          let v1 = VarResFv id' in
          let v2 = eval_assert_aux e2 in
          match e with
          | Equal _ -> EqResFv (v1, v2)
          | Ge _ -> GeResFv (v1, v2)
          | Gt _ -> GtResFv (v1, v2)
          | Le _ -> LeResFv (v1, v2)
          | Lt _ -> LtResFv (v1, v2)
          | _ -> raise Unreachable)
      | Projection (e1, x) -> failwith "Not supported"
      | _ -> (
          let v1, v2 = (eval_assert_aux e1, eval_assert_aux e2) in
          match (v1, v2) with
          | IntResFv i1, IntResFv i2 -> (
              match e with
              | Equal _ -> BoolResFv (i1 = i2)
              | Ge _ -> BoolResFv (i1 >= i2)
              | Gt _ -> BoolResFv (i1 > i2)
              | Le _ -> BoolResFv (i1 <= i2)
              | Lt _ -> BoolResFv (i1 < i2)
              | _ -> raise Unreachable)
          | _ -> raise BadAssert))
  (* TODO: support And/Or (low priority) *)
  | Not e' -> (
      match e' with
      | Var (id', _) when Stdlib.(id = id') -> NotResFv (VarResFv id')
      | _ -> eval_assert_aux e')
  | _ -> raise BadAssert

open ReaderState
open ReaderState.Let_syntax

let cache key data =
  let%bind { c; _ } = get () in
  let%bind () = set_cache (Map.add_exn (Map.remove c key) ~key ~data) in
  let expr, _, _, _ = key in
  (* (match Map.find c key with
     | Some r -> debug (fun m -> m "[Cache] Found: %a" Res.pp r)
     | None -> debug (fun m -> m "[Cache] Not found")); *)
  debug (fun m -> m "[Cache] Add: %a -> %a" Interp.Pp.pp_expr expr Res.pp data);
  return data

let rec analyze_aux ?(caching = true) d expr sigma : Res.t T.t =
  let%bind { v; rerun; iter; _ } = ask () in
  let%bind { c; s; sids; freqs; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  (* debug (fun m -> m "Max depth: %d" !max_d);
     debug (fun m -> m "Level %d" d);
     debug (fun m -> m "S length: %d" (Set.length s)); *)
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  let%bind () = inc_freq (expr, sigma, vid, sid) in
  (* let cache_key = (expr, sigma, vid, sid) in *)
  (* let cache_key = (expr, sigma, v, s) in *)
  let cache_key = (expr, sigma, v, sid) in
  (* debug (fun m -> m "V: %a" V.pp v); *)
  match Map.find c cache_key with
  | Some r
    when caching
         (* when not (exists_lone_stub r) *)
         (* when caching && ((not rerun) || iter = 2) *) ->
      debug (fun m -> m "Cache hit: %a -> %a" Interp.Pp.pp_expr expr Res.pp r);
      return r
  | _ ->
      let%bind r =
        match expr with
        | Int i -> return (single_res (IntAtom i))
        | Bool b -> return (single_res (BoolAtom b))
        | Function (_, _, l) -> return (single_res (FunAtom (expr, l, sigma)))
        | Appl (e, _, l) ->
            info (fun m ->
                m "[Level %d] === App (%a, %d) ===" d Interp.Pp.pp_expr expr l);
            let cycle_label = (l, sigma) in
            let v_state = V_key.Lstate (l, sigma, sid) in
            if Set.mem v v_state then (
              (* App Stub *)
              debug (fun m -> m "Stubbed");
              info (fun m ->
                  m "[Level %d] *** App (%a, %d) ***" d Interp.Pp.pp_expr expr l);
              return (single_res (LStubAtom cycle_label)))
            else (
              (* App *)
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
                    | FunAtom (Function (_, e1, _), _, _) ->
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
              return r2)
        | Var (Ident x, l) ->
            info (fun m ->
                m "[Level %d] === Var (%a) ===" d Interp.Pp.pp_expr expr);
            let cycle_label = (expr, sigma) in
            let est = V_key.Estate (expr, sigma, sid) in
            if Set.mem v est then (
              (* Var Stub *)
              debug (fun m -> m "Stubbed");
              info (fun m ->
                  m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr expr);
              return (single_res (EStubAtom cycle_label)))
            else (
              debug (fun m -> m "Didn't stub");
              match get_myfun l with
              | Some (Function (Ident x1, _, l_myfun)) ->
                  if String.(x = x1) then (
                    (* Var Local *)
                    info (fun m ->
                        m "[Level %d] === Var Local (%a) ===" d
                          Interp.Pp.pp_expr expr);
                    debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                    let s_hd, s_tl = (List.hd_exn sigma, List.tl_exn sigma) in
                    match get_myexpr s_hd with
                    | Appl (_, e2, l') ->
                        debug (fun m -> m "Begin stitching stacks");
                        debug (fun m ->
                            m "Head of candidate fragments must be: %d" l');
                        debug (fun m ->
                            m "Tail of candidate fragments must start with: %a"
                              Sigma.pp s_tl);
                        (* enumerate all matching stacks in the set *)
                        debug (fun m -> m "S: %a" S.pp s);
                        (* the fact that we can prune away "bad" stacks like this
                           makes DDE for program analysis superior *)
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
                              (* stitch the stack to gain more precision *)
                              let%bind rs = acc in
                              let%bind r0 =
                                local d
                                  (fun ({ v; _ } as env) ->
                                    { env with v = Set.add v est })
                                  (analyze_aux ~caching d e2 suf)
                              in
                              return (Set.union rs r0))
                        in
                        (* let r1 = simplify r1 in
                           let%bind { c; _ } = get () in
                           let%bind { v; _ } = ask () in
                           let%bind vid = get_vid v in
                           let c =
                             List.fold sufs ~init:c ~f:(fun acc suf ->
                                 let cache_key = (e2, suf, vid, sid) in
                                 Map.add_exn (Map.remove acc cache_key)
                                   ~key:cache_key ~data:r1)
                           in
                           let%bind () = set_cache c in *)
                        info (fun m ->
                            m "[Level %d] *** Var Local (%a) ***" d
                              Interp.Pp.pp_expr expr);
                        let r1 = elim_stub r1 (St.Estate cycle_label) in
                        debug (fun m -> m "[Var Local] r1: %a" Res.pp r1);
                        info (fun m ->
                            m "[Level %d] *** Var (%a) ***" d Interp.Pp.pp_expr
                              expr);
                        return r1
                    | _ -> raise Unreachable [@coverage off])
                  else (
                    (* Var Non-Local *)
                    info (fun m ->
                        m "[Level %d] === Var Non-Local (%a) ===" d
                          Interp.Pp.pp_expr expr);
                    debug (fun m -> m "sigma: %a" Sigma.pp sigma);
                    debug (fun m -> m "Reading App at front of sigma");
                    match get_myexpr (List.hd_exn sigma) with
                    | Appl (e1, _, l2) ->
                        debug (fun m ->
                            m "Function being applied at front of sigma: %a"
                              Interp.Pp.pp_expr e1);
                        let e1st = V_key.Estate (e1, sigma, sid) in
                        if Set.mem v e1st (* && rerun = 2 *) then (
                          debug (fun m -> m "[Var Non-Local] Stubbed e1");
                          info (fun m ->
                              m "[Level %d] *** Var Non-Local (%a) ***" d
                                Interp.Pp.pp_expr expr);
                          info (fun m ->
                              m "[Level %d] *** Var (%s, %d) ***" d x l);
                          return (single_res (EStubAtom (e1, sigma))))
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
                                    (fun ({ v; rerun; iter; _ } as env) ->
                                      {
                                        env with
                                        v = Set.add v e1st;
                                        rerun = true;
                                        iter = iter + 1;
                                      })
                                    (analyze_aux ~caching d e1 suf)
                                in
                                debug (fun m ->
                                    m "[Var Non-Local] r0: %a" Res.pp r0);
                                return (Set.union rs r0))
                          in
                          let r1 = simplify r1 in
                          (* let%bind { c; _ } = get () in
                             let c =
                               List.fold sufs ~init:c ~f:(fun acc suf ->
                                   let cache_key = (e1, suf, vid, sid) in
                                   Map.add_exn (Map.remove acc cache_key)
                                     ~key:cache_key ~data:r1)
                             in
                             let%bind () = set_cache c in *)
                          debug (fun m -> m "r1 length: %d" (Set.length r1));
                          debug (fun m ->
                              m
                                "[Level %d] Found all stitched stacks and \
                                 evaluated e1, begin relabeling variables"
                                d);
                          let%bind r2 =
                            Set.fold r1 ~init:(return empty_res)
                              ~f:(fun acc a ->
                                debug (fun m ->
                                    m
                                      "[Level %d] Visiting 1 possible function \
                                       for e1:"
                                      d);
                                debug (fun m -> m "%a" Atom.pp a);
                                match a with
                                | FunAtom
                                    (Function (Ident x1', _, l1), _, sigma1) ->
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
                              m "[Level %d] *** Var (%a) ***" d
                                Interp.Pp.pp_expr expr);
                          let r2 = elim_stub r2 (St.Estate cycle_label) in
                          debug (fun m -> m "[Var Non-Local] r2: %a" Res.pp r2);
                          return r2
                    | _ -> raise Unreachable [@coverage off])
              | _ -> raise Unreachable [@coverage off])
        | If (e, e_true, e_false, l) -> (
            debug (fun m -> m "[Level %d] === If ===" d);
            let%bind r_cond = analyze_aux ~caching d e sigma in
            match Set.elements r_cond with
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
            | _ ->
                debug (fun m -> m "[Level %d] === If Both ===" d);
                let%bind r_true = analyze_aux ~caching d e_true sigma in
                let%bind r_false = analyze_aux ~caching d e_false sigma in
                debug (fun m -> m "[Level %d] *** If Both ***" d);
                return (Set.union r_true r_false))
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
            info (fun m ->
                m "[Level %d] === Binop (%a) ===" d Interp.Pp.pp_expr expr);
            let%bind r1 = analyze_aux ~caching d e1 sigma in
            let%bind r2 = analyze_aux ~caching d e2 sigma in
            debug (fun m ->
                m "[Level %d] Evaluated binop to (%a <op> %a)" d Res.pp r1
                  Res.pp r2);
            info (fun m ->
                m "[Level %d] *** Binop (%a) ***" d Interp.Pp.pp_expr expr);
            return
              (match expr with
              | Plus _ -> all_combs_int r1 r2 ( + )
              | Minus _ -> all_combs_int r1 r2 ( - )
              | Mult _ -> all_combs_int r1 r2 ( * )
              | And _ -> all_combs_bool r1 r2 ( && )
              | Or _ -> all_combs_bool r1 r2 ( || )
              | Equal _ -> all_combs_bool' r1 r2 ( = )
              | Ge _ -> all_combs_bool' r1 r2 ( >= )
              | Gt _ -> all_combs_bool' r1 r2 ( > )
              | Le _ -> all_combs_bool' r1 r2 ( <= )
              | Lt _ -> all_combs_bool' r1 r2 ( < )
              | _ -> raise Unreachable [@coverage off])
        | Not e ->
            let%bind r = analyze_aux ~caching d e sigma in
            return
              (match Set.elements r with
              | [] -> empty_res
              | [ BoolAtom b ] -> single_res (BoolAtom (not b))
              | _ -> bool_tf_res)
        | Record es ->
            es
            |> List.fold_right ~init:(return []) ~f:(fun (id, ei) acc ->
                   let%bind rs = acc in
                   let%bind r = analyze_aux ~caching d ei sigma in
                   return ((id, r) :: rs))
            |> fun rs ->
            let%bind rs = rs in
            return (single_res (RecAtom rs))
        | Projection (e, (Ident x as id)) ->
            debug (fun m -> m "[Level %d] === Proj ===" d);
            let%bind r0 = analyze_aux ~caching d e sigma in
            debug (fun m -> m "[Level %d][Proj] r0: %a.%s" d Res.pp r0 x);
            debug (fun m -> m "[Level %d] *** Proj ***" d);
            return (single_res (ProjAtom (r0, id)))
        | Inspection ((Ident x as id), e) ->
            debug (fun m -> m "[Level %d] === Insp ===" d);
            let%bind r0 = analyze_aux ~caching d e sigma in
            debug (fun m -> m "[Level %d][Insp] r0: %s in %a" d x Res.pp r0);
            debug (fun m -> m "[Level %d] *** Insp ***" d);
            return (single_res (InspAtom (id, r0)))
        | LetAssert (id, e1, e2) ->
            let%bind r1 = analyze_aux ~caching d e1 sigma in
            let r2 = eval_assert e2 id in
            return (single_res (AssertAtom (id, r1, r2)))
        | Let _ -> raise Unreachable [@coverage off]
      in
      cache cache_key (simplify r)

let analyze ?(caching = true) e =
  let e = transform_let e in
  build_myfun e None;
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  let empty_v = Set.empty (module V_key) in
  let empty_s = Set.empty (module Sigma) in

  let start_time = Stdlib.Sys.time () in
  let r, { sids; freqs; _ } =
    analyze_aux ~caching 0 e []
      {
        v = empty_v;
        vids = Map.singleton (module V) empty_v 0;
        cnt = 1;
        rerun = false;
        iter = 0;
      }
      {
        c = Map.empty (module Cache_key);
        s = empty_s;
        sids = Map.singleton (module S) empty_s 0;
        cnt = 1;
        freqs = Map.empty (module Freq_key);
      }
  in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  debug (fun m -> m "Result: %a" Res.pp r);

  (* debug (fun m -> m "freqs:");
     log_freqs freqs;
     debug (fun m -> m "sids:");
     log_sids sids ~size:false; *)
  clean_up ();

  (r, runtime)
