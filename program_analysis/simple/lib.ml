open Core
open Logs
open Interp.Ast
open Pa.Exns
open Pa.Logging
open Grammar
open Utils
open Solver
open Simplifier

(* max recursion depth ever reached by execution *)
let max_d = ref 0

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

(** only allows the following forms:
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

let log_v_set = Set.iter ~f:(fun st -> debug (fun m -> m "%s" (V_key.show st)))

let elim_stub r label =
  if not (exists_stub r label) then r
  else
    let bases =
      Set.fold r ~init:empty_res ~f:(fun acc a ->
          match a with
          | RecAtom _ when not (exists_stub (single_res a) label) ->
              Set.add acc a
          | ProjAtom (r, Ident key) when not (exists_stub r label) -> (
              match unwrap_res r with
              | [ RecAtom rs ] -> (
                  match
                    List.find rs ~f:(fun (Ident key', _) -> String.(key = key'))
                  with
                  | Some (_, r') when Set.length r' = 1 ->
                      Set.add acc (r' |> unwrap_res |> List.hd_exn)
                  | _ -> raise Runtime_error)
              | _ -> acc)
          | FunAtom _ -> Set.add acc a
          | _ -> acc)
    in
    Set.fold r ~init:empty_res ~f:(fun acc a ->
        match a with
        | ProjAtom (r, Ident key) -> (
            match unwrap_res r with
            | [ EStubAtom st ] when St.(label = Estate st) ->
                Set.fold bases ~init:acc ~f:(fun acc -> function
                  | RecAtom es -> (
                      match
                        List.find es ~f:(fun (Ident key', _) ->
                            String.(key = key'))
                      with
                      | Some (_, r) -> Set.union acc r
                      | None -> acc)
                  | _ -> raise Runtime_error)
            | _ -> Set.add acc a)
        (* (fun x -> x) | stub *)
        | EStubAtom st when St.(label = Estate st) -> acc
        | _ -> Set.add acc a)

module ReaderState = struct
  module T = struct
    type cache = Res.t Map.M(Cache_key).t
    type vids = string Map.M(V).t
    type sids = string Map.M(S).t
    type freqs = int64 Map.M(Freq_key).t
    type env = { v : V.t; vids : vids; cnt : int }
    type state = { s : S.t; c : cache; freqs : freqs; sids : sids; cnt : int }
    type 'a t = env -> state -> 'a * state

    let return (a : 'a) : 'a t = fun _ st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun env st ->
      let a, st' = m env st in
      f a env st'

    let map = `Define_using_bind
    let ask () : env t = fun env st -> (env, st)

    let local (f : env -> env) (m : 'a t) : 'a t =
     fun env st ->
      let ({ v; vids; cnt } as env') = f env in
      let vids', cnt' =
        if Map.mem vids v then (vids, cnt)
        else (Map.add_exn vids ~key:v ~data:(Format.sprintf "V%d" cnt), cnt + 1)
      in
      m { env' with vids = vids'; cnt = cnt' } st

    let get () : state t = fun _ st -> (st, st)
    let get_vid v : string t = fun { vids; _ } st -> (Map.find_exn vids v, st)

    let get_sid s : string t =
     fun _ ({ sids; _ } as st) -> (Map.find_exn sids s, st)

    let set_s s : unit t =
     fun _ ({ sids; cnt; _ } as st) ->
      let sids', cnt' =
        if Map.mem sids s then (sids, cnt)
        else (Map.add_exn sids ~key:s ~data:(Format.sprintf "S%d" cnt), cnt + 1)
      in
      ((), { st with s; sids = sids'; cnt = cnt' })

    let set_cache c : unit t = fun _ st -> ((), { st with c })

    let inc_freq freq_key : unit t =
     fun _ ({ freqs; _ } as st) ->
      let freqs' =
        match Map.find freqs freq_key with
        | None -> Map.add_exn freqs ~key:freq_key ~data:1L
        | Some freq ->
            Map.add_exn
              (Map.remove freqs freq_key)
              ~key:freq_key
              ~data:Int64.(freq + 1L)
      in
      ((), { st with freqs = freqs' })
  end

  include T
  include Monad.Make (T)
end

open ReaderState
open ReaderState.Let_syntax

let cache key data =
  let%bind { c; _ } = get () in
  let%bind () = set_cache (Map.add_exn (Map.remove c key) ~key ~data) in
  return data

let print_freqs ?(sort = true) freqs =
  freqs |> Map.to_alist |> fun freqs ->
  (if not sort then freqs
   else
     List.sort freqs ~compare:(fun (_, freq1) (_, freq2) ->
         Int64.descending freq1 freq2))
  |> List.iter ~f:(fun ((e, sigma, vid, sid), freq) ->
         Format.printf "(%a, %a, %s, %s) -> %Ld\n" Interp.Pp.pp_expr e pp_sigma
           sigma vid sid freq)

let print_vids ?(size = false) ?(sort = false) vids =
  vids |> Map.to_alist |> fun vids ->
  (if not sort then vids
   else
     List.sort vids ~compare:(fun (_, id1) (_, id2) ->
         String.descending id1 id2))
  |> List.iter ~f:(fun (key, data) ->
         if size then Format.printf "%d -> %s\n" (Set.length key) data
         else Format.printf "%s -> %s\n" (V.show key) data)

let print_sids ?(size = false) =
  Map.iteri ~f:(fun ~key ~data ->
      if size then Format.printf "%d -> %s\n" (Set.length key) data
      else Format.printf "%s -> %s\n" (S.show key) data)

let start_time = ref (Stdlib.Sys.time ())
let bool_tf_res = Set.of_list (module Res_key) [ BoolAtom true; BoolAtom false ]

let all_combs_int r1 r2 op =
  let open Atom in
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | IntAtom b1, IntAtom b2 -> Set.add acc (IntAtom (op b1 b2))
          | _ -> Set.add acc IntAnyAtom))

let all_combs_bool r1 r2 op =
  let open Atom in
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | BoolAtom b1, BoolAtom b2 -> Set.add acc (BoolAtom (op b1 b2))
          | _ -> Set.union acc bool_tf_res))

let all_combs_bool' r1 r2 op =
  let open Atom in
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | IntAtom i1, IntAtom i2 -> Set.add acc (BoolAtom (op i1 i2))
          | _ -> Set.union acc bool_tf_res))

(* (true | false) && true *)

let rec analyze_aux d expr sigma pi : Res.t T.t =
  let%bind { v; vids; _ } = ask () in
  let%bind { c; s; sids; freqs; _ } = get () in
  let d = d + 1 in
  if d > !max_d then max_d := d;
  (* Logs.debug (fun m -> m "Max %d" !max_d); *)
  (* Logs.debug (fun m -> m "Level %d" d); *)
  (* Logs.debug (fun m -> m "S length: %d" (Set.length s)); *)
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  let%bind () = inc_freq (expr, sigma, vid, sid) in
  let cache_key = (expr, sigma, vid, sid) in
  match Map.find c cache_key with
  | Some r ->
      (* Logs.debug (fun m -> m "Cache hit"); *)
      return r
  | None ->
      let%bind r =
        match expr with
        | Int i -> return (single_res (IntAtom i))
        | Bool b -> return (single_res (BoolAtom b))
        | Function (_, _, l) -> return (single_res (FunAtom (expr, l, sigma)))
        | Appl (e, _, l) ->
            info (fun m ->
                m "[Level %d] === Appl (%a) ====" d Interp.Pp.pp_expr expr);
            let cycle_label = (l, sigma) in
            let v_state = V_key.Lstate (l, sigma, sid) in
            if Set.mem v v_state then (
              (* App Stub *)
              debug_plain "Stubbed";
              info (fun m ->
                  m "[Level %d] *** Appl (%a) ****" d Interp.Pp.pp_expr expr);
              return (single_res (LStubAtom cycle_label)))
            else (
              (* App *)
              debug_plain "Didn't stub";
              debug (fun m -> m "sigma: %a" pp_sigma sigma);
              let sigma' = l :: sigma in
              let pruned_sigma' = prune_sigma sigma' in
              debug (fun m -> m "sigma_pruned': %a" pp_sigma pruned_sigma');
              debug (fun m ->
                  m "Evaluating function being applied: %a" Interp.Pp.pp_expr e);
              let%bind r1 = analyze_aux d e sigma pi in
              debug (fun m -> m "[Appl] r1 length: %d" (Set.length r1));
              let%bind { s = s1; _ } = get () in
              let v_state_s = Set.add s1 pruned_sigma' in
              let%bind () = set_s v_state_s in
              let%bind v_state_sid = get_sid v_state_s in
              let v_new = V_key.Lstate (l, sigma, v_state_sid) in
              let%bind r2 =
                Set.fold r1 ~init:(return empty_res) ~f:(fun acc a ->
                    debug (fun m ->
                        m
                          "[Level %d] [Appl] Evaluating 1 possible function \
                           being applied:"
                          d);
                    debug (fun m -> m "%a" pp_atom a);
                    match a with
                    | FunAtom (Function (_, e1, _), _, _) ->
                        debug (fun m ->
                            m
                              "[Appl] Evaluating body of function being \
                               applied: %a"
                              Interp.Pp.pp_expr e1);
                        let%bind acc_r = acc in
                        let%bind r0 =
                          local
                            (fun ({ v; _ } as env) ->
                              { env with v = Set.add v v_new })
                            (analyze_aux d e1 pruned_sigma' pi)
                        in
                        return (Set.union acc_r r0)
                    | _ -> acc)
              in
              let r2 = elim_stub r2 (St.Lstate cycle_label) in
              debug (fun m -> m "[Appl] r2: %a" pp_res (unwrap_res r2));
              info (fun m ->
                  m "[Level %d] *** Appl (%a) ****" d Interp.Pp.pp_expr expr);
              return r2)
        | Var (Ident x, l) ->
            info (fun m -> m "[Level %d] === Var (%s, %d) ====" d x l);
            let cycle_label = (expr, sigma) in
            let est = V_key.Estate (expr, sigma, sid) in
            if Set.mem v est then (
              (* Var Stub *)
              debug_plain "Stubbed";
              info (fun m -> m "[Level %d] *** Var (%s, %d) ****" d x l);
              return (single_res (EStubAtom cycle_label)))
            else (
              debug_plain "Didn't stub";
              match get_myfun l with
              | Some (Function (Ident x1, _, l_myfun)) ->
                  if String.(x = x1) then (
                    (* Var Local *)
                    info (fun m ->
                        m "[Level %d] === Var Local (%s, %d) ====" d x l);
                    debug (fun m -> m "sigma: %a" pp_sigma sigma);
                    let s_hd, s_tl = (List.hd_exn sigma, List.tl_exn sigma) in
                    match get_myexpr s_hd with
                    | Appl (_, e2, l') ->
                        let%bind r1 =
                          debug_plain "Begin stitching stacks";
                          debug (fun m ->
                              m "Head of candidate fragments must be: %d" l');
                          debug (fun m ->
                              m
                                "Tail of candidate fragments must start with: \
                                 %a"
                                pp_sigma s_tl);
                          (* enumerate all matching stacks in the set *)
                          debug (fun m -> m "S len: %d" (Set.length s));
                          debug (fun m -> m "S: %s" (S.show s));
                          Set.fold s ~init:(return empty_res)
                            ~f:(fun acc sigma_i ->
                              let sigma_i_hd, sigma_i_tl =
                                (List.hd_exn sigma_i, List.tl_exn sigma_i)
                              in
                              (* the fact that we can prune away "bad" stacks like this
                                 makes DDE for program analysis superior *)
                              if sigma_i_hd = l' && starts_with sigma_i_tl s_tl
                              then (
                                debug (fun m ->
                                    m
                                      "[Level %d] Stitched! Evaluating Appl \
                                       argument, using stitched stack %a:"
                                      d pp_sigma sigma_i_tl);
                                debug (fun m -> m "%a" Interp.Pp.pp_expr e2);
                                (* stitch the stack to gain more precision *)
                                let%bind acc_r = acc in
                                let%bind r0 =
                                  local
                                    (fun ({ v; _ } as env) ->
                                      { env with v = Set.add v est })
                                    (analyze_aux d e2 sigma_i_tl pi)
                                in
                                return (Set.union acc_r r0))
                              else acc)
                        in
                        info (fun m ->
                            m "[Level %d] *** Var Local (%s, %d) ****" d x l);
                        let r1 = elim_stub r1 (St.Estate cycle_label) in
                        debug (fun m ->
                            m "[Var Local] r1: %a" pp_res (unwrap_res r1));
                        info (fun m ->
                            m "[Level %d] *** Var (%s, %d) ****" d x l);
                        return r1
                    | _ -> raise Unreachable [@coverage off])
                  else (
                    (* Var Non-Local *)
                    info (fun m ->
                        m "[Level %d] === Var Non-Local (%s, %d) ====" d x l);
                    debug (fun m -> m "sigma: %a" pp_sigma sigma);
                    debug_plain "Reading Appl at front of sigma";
                    match get_myexpr (List.hd_exn sigma) with
                    | Appl (e1, _, l2) ->
                        debug_plain "Function being applied at front of sigma:";
                        debug (fun m -> m "%a" Interp.Pp.pp_expr e1);
                        debug (fun m -> m "%a" Interp.Ast.pp_expr e1);
                        if Set.mem v (V_key.Estate (e1, sigma, sid)) then (
                          debug_plain "Stubbed e1";
                          return (single_res (EStubAtom (e1, sigma))))
                        else
                          let sigma_tl = List.tl_exn sigma in
                          debug_plain "Begin stitching stacks";
                          (* enumerate all matching stacks in the set *)
                          debug (fun m -> m "S len: %d" (Set.length s));
                          debug (fun m -> m "S: %s" (S.show s));
                          let%bind r1 =
                            Set.fold s ~init:(return empty_res)
                              ~f:(fun acc sigma_i ->
                                debug (fun m ->
                                    m "sigma_i: %s" (S_key.show sigma_i));
                                let sigma_i_hd, sigma_i_tl =
                                  (List.hd_exn sigma_i, List.tl_exn sigma_i)
                                in
                                (* stitch the stack to gain more precision *)
                                if
                                  sigma_i_hd = l2
                                  && starts_with sigma_i_tl sigma_tl
                                then (
                                  debug (fun m ->
                                      m
                                        "[Level %d] Stitched! Evaluating \
                                         function being applied at front of \
                                         sigma, using stitched stack %a"
                                        d pp_sigma sigma_i_tl);
                                  let%bind acc_r = acc in
                                  let%bind r0 =
                                    local
                                      (fun ({ v; _ } as env) ->
                                        { env with v = Set.add v est })
                                      (analyze_aux d e1 sigma_i_tl pi)
                                  in
                                  return (Set.union acc_r r0))
                                else acc)
                          in
                          (* TODO: Eval(r1) *)
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
                                debug (fun m -> m "%a" pp_atom a);
                                match a with
                                | FunAtom
                                    (Function (Ident x1', _, l1), _, sigma1) ->
                                    if Stdlib.(x1 = x1') && l_myfun = l1 then (
                                      debug (fun m ->
                                          m
                                            "[Var Non-Local] Relabel %s with \
                                             label %d and evaluate"
                                            x l1);
                                      let%bind acc_r = acc in
                                      let%bind r0' =
                                        local
                                          (fun ({ v; _ } as env) ->
                                            { env with v = Set.add v est })
                                          (analyze_aux d
                                             (Var (Ident x, l1))
                                             sigma1 pi)
                                      in
                                      return (Set.union acc_r r0'))
                                    else acc
                                | _ -> acc)
                          in
                          info (fun m ->
                              m "[Level %d] *** Var Non-Local (%s, %d) ****" d x
                                l);
                          info (fun m ->
                              m "[Level %d] *** Var (%s, %d) ****" d x l);
                          let r2 = elim_stub r2 (St.Estate cycle_label) in
                          debug (fun m ->
                              m "[Var Non-Local] r2: %a" pp_res (unwrap_res r2));
                          return r2
                    | _ -> raise Unreachable [@coverage off])
              | _ -> raise Unreachable [@coverage off])
        | If (e, e_true, e_false, l) -> (
            debug (fun m -> m "[Level %d] === If ===" d);
            let%bind r_cond = analyze_aux d e sigma None in
            match unwrap_res r_cond with
            | [ BoolAtom b ] ->
                debug (fun m -> m "[Level %d] === If %b ===" d b);
                if b then (
                  let%bind r_true = analyze_aux d e_true sigma None in
                  debug (fun m -> m "[Level %d] *** If %b ***" d b);
                  return r_true)
                else
                  let%bind r_false = analyze_aux d e_false sigma None in
                  debug (fun m -> m "[Level %d] *** If %b ***" d b);
                  return r_false
            | _ ->
                debug (fun m -> m "[Level %d] === If Both ===" d);
                (* Format.printf "r_cond: %a\n" pp_res r_cond; *)
                let%bind r_true = analyze_aux d e_true sigma None in
                let%bind r_false = analyze_aux d e_false sigma None in
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
                m "[Level %d] === Binop (%a) ====" d Interp.Pp.pp_expr expr);
            let%bind r1 = analyze_aux d e1 sigma pi in
            let%bind r2 = analyze_aux d e2 sigma pi in
            debug (fun m ->
                m "[Level %d] Evaluated binop to (%a <op> %a)" d Utils.pp_res
                  (unwrap_res r1) Utils.pp_res (unwrap_res r2));
            info (fun m ->
                m "[Level %d] *** Binop (%a) ****" d Interp.Pp.pp_expr expr);
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
            let%bind r = analyze_aux d e sigma pi in
            return
              (match unwrap_res r with
              | [] -> empty_res
              | [ BoolAtom b ] -> single_res (BoolAtom (not b))
              | _ -> bool_tf_res)
        | Record es ->
            (* if List.is_empty es then return (single_res (RecAtom []))
               else *)
            es
            |> List.fold_right ~init:(return []) ~f:(fun (id, ei) acc ->
                   let%bind rs = acc in
                   let%bind r = analyze_aux d ei sigma pi in
                   return ((id, r) :: rs))
            |> fun rs ->
            let%bind rs = rs in
            return (single_res (RecAtom rs))
        | Projection (e, (Ident x as id)) ->
            debug (fun m -> m "[Level %d] === Proj ===" d);
            let%bind r0 = analyze_aux d e sigma pi in
            debug (fun m ->
                m "[Level %d][Proj] r0: %a.%s" d pp_res (unwrap_res r0) x);
            debug (fun m -> m "[Level %d] *** Proj ***" d);
            return (single_res (ProjAtom (r0, id)))
        | Inspection ((Ident x as id), e) ->
            debug (fun m -> m "[Level %d] === Insp ===" d);
            let%bind r0 = analyze_aux d e sigma pi in
            debug (fun m ->
                m "[Level %d][Insp] r0: %s in %a" d x pp_res (unwrap_res r0));
            debug (fun m -> m "[Level %d] *** Insp ***" d);
            return (single_res (InspAtom (id, r0)))
        | LetAssert (id, e1, e2) ->
            let%bind r1 = analyze_aux d e1 sigma pi in
            let r2 = eval_assert e2 id in
            return (single_res (AssertAtom (id, r1, r2)))
        | Let _ -> raise Unreachable [@coverage off]
      in
      cache cache_key (simplify r)

let analyze ?(debug_mode = false) ?(verify = true) ?(test_num = 0)
    ?(should_cache = true) e =
  is_debug_mode := debug_mode;

  let e = transform_let e in
  build_myfun e None;
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  (* Format.printf "%a\n" pp_expr e; *)
  start_time := Stdlib.Sys.time ();
  let empty_v = Set.empty (module V_key) in
  let empty_s = Set.empty (module S_key) in
  let r, { sids; freqs; _ } =
    analyze_aux 0 e [] None
      { v = empty_v; vids = Map.singleton (module V) empty_v "V0"; cnt = 1 }
      {
        s = Set.empty (module S_key);
        c = Map.empty (module Cache_key);
        sids = Map.singleton (module S) empty_s "S0";
        cnt = 1;
        freqs = Map.empty (module Freq_key);
      }
  in

  (* print_freqs freqs; *)

  (* Format.printf "sids:\n";
     print_sids sids ~size:false; *)

  (* Format.printf "vids:\n";
     print_vids vids ~size:false; *)

  (* let r = simplify r in *)
  (* dot_of_result test_num r; *)
  debug (fun m -> m "Result: %a" Utils.pp_res (unwrap_res r));
  (* debug (fun m -> m "Result: %a" Grammar.pp_res r); *)
  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" (show_expr e);
     Format.printf "****** Label Table ******\n";
     Interp.Lib.print_myexpr myexpr;
     Format.printf "****** Label Table ******\n\n"))
  [@coverage off];

  clean_up ();

  (* if verify then verify_result r; *)
  r
