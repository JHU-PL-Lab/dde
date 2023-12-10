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
  if exists_stub r label then
    (* Format.printf "elim_stub: %a\n" pp_res r; *)
    (* Format.printf "label: %a\n" St.pp label; *)
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
    let r' =
      Set.fold r ~init:empty_res ~f:(fun acc a ->
          match a with
          | ProjAtom (r, Ident key) -> (
              match unwrap_res r with
              | [ EStubAtom st ] when St.(label = Estate st) ->
                  Set.fold bases ~init:empty_res ~f:(fun acc -> function
                    | RecAtom es -> (
                        match
                          List.find es ~f:(fun (Ident key', _) ->
                              String.(key = key'))
                        with
                        | Some (_, r) -> Set.union acc r
                        | None ->
                            acc
                            (* Format.printf "base: %a\n" pp_atom base;
                               raise Runtime_error *))
                    | _ -> raise Runtime_error)
              | _ -> Set.add acc a)
          (* (fun x -> x) | stub *)
          | EStubAtom st when St.(label = Estate st) -> acc
          | _ -> Set.add acc a)
    in
    (* Format.printf "result: %a\n" pp_res r'; *)
    r'
  else r

module With_state = struct
  module T = struct
    type cache = Res.t Map.M(Cache_key).t
    type vids = int Map.M(V).t
    type sids = int Map.M(S).t
    type freqs = int64 Map.M(Freq_key).t

    type state = {
      s : S.t;
      v : V.t;
      c : cache;
      freqs : freqs;
      sids : sids;
      vids : vids;
      cnt : int;
    }

    type 'a t = state -> 'a * state

    let return (a : 'a) : 'a t = fun st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun st ->
      let a, ({ s; v; sids; vids; cnt; _ } as st') = m st in
      let sids', cnt' =
        if Map.mem sids s then (sids, cnt)
        else (Map.add_exn sids ~key:s ~data:cnt, cnt + 1)
      in
      let vids', cnt' =
        if Map.mem vids v then (vids, cnt')
        else (Map.add_exn vids ~key:v ~data:cnt', cnt' + 1)
      in
      f a { st' with sids = sids'; vids = vids'; cnt = cnt' }

    let map = `Define_using_bind
    let get () : state t = fun st -> (st, st)

    let get_cnt () : int t =
     fun ({ cnt; _ } as st) -> (cnt, { st with cnt = cnt + 1 })

    let get_vid v : int t = fun ({ vids; _ } as st) -> (Map.find_exn vids v, st)
    let get_sid s : int t = fun ({ sids; _ } as st) -> (Map.find_exn sids s, st)
    let set_s s : unit t = fun st -> ((), { st with s })
    let set_v v : unit t = fun st -> ((), { st with v })
    let set_cache c : unit t = fun st -> ((), { st with c })
    let set_vids vids : unit t = fun st -> ((), { st with vids })
    let set_sids sids : unit t = fun st -> ((), { st with sids })
    let set_freqs freqs : unit t = fun st -> ((), { st with freqs })

    let inc_freq freq_key : unit t =
     fun ({ freqs; _ } as st) ->
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

open With_state
open With_state.Let_syntax

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
         Format.printf "(%a, %a, %d, %d) -> %Ld\n" Interp.Pp.pp_expr e pp_sigma
           sigma vid sid freq)

let print_vids ?(size = false) ?(sort = false) vids =
  vids |> Map.to_alist |> fun vids ->
  (if not sort then vids
   else
     List.sort vids ~compare:(fun (_, id1) (_, id2) -> Int.descending id1 id2))
  |> List.iter ~f:(fun (key, data) ->
         if size then Format.printf "%d -> %d\n" (Set.length key) data
         else Format.printf "%s -> %d\n" (V.show key) data)

let print_sids ?(size = false) =
  Map.iteri ~f:(fun ~key ~data ->
      if size then Format.printf "%d -> %d\n" (Set.length key) data
      else Format.printf "%s -> %d\n" (S.show key) data)

let start_time = ref (Stdlib.Sys.time ())

let rec analyze_aux d expr sigma pi : Res.t T.t =
  let d = d + 1 in
  let%bind { c; s; v; sids; vids; freqs; _ } = get () in
  (* if Float.(Stdlib.Sys.time () - !start_time > 120.) then (
     print_freqs freqs ~sort:true;
     Format.printf "vids:\n";
     print_vids vids ~size:true ~sort:true;
     Format.printf "sids:\n";
     print_sids sids;
     failwith "timed out"); *)
  (* Logs.debug (fun m -> m "Level %d" d); *)
  (* Logs.debug (fun m -> m "S length: %d" (Set.length s)); *)
  (* if d >= 100 then gen_logs := true; *)
  (* if Set.length s >= 23 then gen_logs := true; *)
  if d > !max_d then max_d := d;
  (* Logs.debug (fun m -> m "max d: %d" !max_d); *)
  let%bind vid = get_vid v in
  let%bind sid = get_sid s in
  let%bind () = inc_freq (expr, sigma, vid, sid) in
  let cache_key = (expr, sigma, vid, sid) in
  match Map.find c cache_key with
  | Some r ->
      debug (fun m -> m "Cache hit");
      return r
  | None ->
      let%bind r =
        match expr with
        | Int i -> return (single_res IntAnyAtom)
        | Bool b -> return (single_res (BoolAtom b))
        | Function (_, _, l) -> return (single_res (FunAtom (expr, l, sigma)))
        | Appl (e, _, l) ->
            info (fun m ->
                m "[Level %d] === Appl (%a) ====" d Interp.Pp.pp_expr expr);
            let cycle_label = (l, sigma) in
            let v_state = V_key.Lstate (l, sigma, sid) in
            (* TODO: try two-pass mechanism again *)
            if Set.mem v v_state then (
              debug_plain "Stubbed";
              info (fun m ->
                  m "[Level %d] *** Appl (%a) ****" d Interp.Pp.pp_expr expr);
              return (single_res (LStubAtom cycle_label)))
            else (
              (* Application *)
              debug_plain "Didn't stub";
              debug (fun m -> m "sigma: %s" (show_sigma sigma));
              let sigma' = l :: sigma in
              let pruned_sigma' = prune_sigma sigma' in
              debug (fun m -> m "sigma_pruned': %s" (show_sigma pruned_sigma'));
              debug (fun m ->
                  m "Evaluating function being applied: %a" Interp.Pp.pp_expr e);
              debug (fun m ->
                  m "Evaluating function being applied: %a" Interp.Ast.pp_expr e);
              let%bind () = set_v (Set.add v v_state) in
              let%bind r1 = analyze_aux d e sigma pi in
              debug (fun m -> m "[Appl] r1 length: %d" (Set.length r1));
              let%bind { s = s1; _ } = get () in
              let v_state_s = Set.add s1 pruned_sigma' in
              let%bind () = set_s v_state_s in
              let%bind v_state_sid = get_sid v_state_s in
              let%bind () =
                set_v (Set.add v (V_key.Lstate (l, sigma, v_state_sid)))
              in
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
                        let%bind acc = acc in
                        debug (fun m ->
                            m
                              "[Appl] Evaluating body of function being \
                               applied: %a"
                              Interp.Pp.pp_expr e1);
                        analyze_aux d e1 pruned_sigma' pi
                    | _ -> acc)
              in
              let r2 = elim_stub r2 (St.Lstate cycle_label) in
              debug (fun m -> m "r2: %a" pp_res (unwrap_res r2));
              info (fun m ->
                  m "[Level %d] *** Appl (%a) ****" d Interp.Pp.pp_expr expr);
              return r2)
        | Var (Ident x, l) ->
            info (fun m -> m "[Level %d] === Var (%s, %d) ====" d x l);
            let cycle_label = (expr, sigma) in
            let est = V_key.Estate (expr, sigma, sid) in
            let%bind () = set_v (Set.add v est) in
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
                    debug (fun m -> m "sigma: %s" (show_sigma sigma));
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
                                 %s"
                                (show_sigma s_tl));
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
                                      "[Level %d] [Round %d] Stitched! \
                                       Evaluating Appl argument, using \
                                       stitched stack %s:"
                                      d 0 (show_sigma sigma_i_tl));
                                debug (fun m -> m "%a" Interp.Pp.pp_expr e2);
                                (* stitch the stack to gain more precision *)
                                let%bind r0 = analyze_aux d e2 sigma_i_tl pi in
                                let%bind acc' = acc in
                                return (Set.union acc' r0))
                              else acc)
                        in
                        info (fun m ->
                            m "[Level %d] *** Var Local (%s, %d) ****" d x l);
                        info (fun m ->
                            m "[Level %d] *** Var (%s, %d) ****" d x l);
                        let r1 = elim_stub r1 (St.Estate cycle_label) in
                        debug (fun m -> m "r1: %a" pp_res (unwrap_res r1));
                        return r1
                    | _ -> raise Unreachable [@coverage off])
                  else (
                    (* Var Non-Local *)
                    info (fun m ->
                        m "[Level %d] === Var Non-Local (%s, %d) ====" d x l);
                    debug (fun m -> m "sigma: %s" (show_sigma sigma));
                    debug_plain "Reading Appl at front of sigma";
                    match get_myexpr (List.hd_exn sigma) with
                    | Appl (e1, _, l2) ->
                        debug_plain "Function being applied at front of sigma:";
                        debug (fun m -> m "%a" Interp.Pp.pp_expr e1);
                        debug (fun m -> m "%a" Interp.Ast.pp_expr e1);
                        let est = V_key.Estate (e1, sigma, sid) in
                        if Set.mem v est then (
                          debug_plain "Stubbed e1";
                          return (single_res (EStubAtom (e1, sigma))))
                        else
                          let sigma_tl = List.tl_exn sigma in
                          debug_plain "Begin stitching stacks";
                          (* let new_v = Set.add new_v est in *)
                          (* enumerate all matching stacks in the set *)
                          debug (fun m -> m "S len: %d" (Set.length s));
                          debug (fun m -> m "S: %s" (S.show s));
                          let%bind r1 =
                            Set.fold s ~init:(return empty_res)
                              ~f:(fun acc sigma_i ->
                                debug (fun m ->
                                    m "[Round %d] sigma_i: %s" 0
                                      (S_key.show sigma_i));
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
                                         sigma, using stitched stack %s"
                                        d (show_sigma sigma_i_tl));
                                  let%bind r0 =
                                    analyze_aux d e1 sigma_i_tl pi
                                  in
                                  let%bind acc' = acc in
                                  return (Set.union acc' r0))
                                else (
                                  debug (fun m ->
                                      m "[Level %d] Didn't stitch!" d);
                                  acc))
                          in
                          debug (fun m ->
                              m
                                "[Level %d] Found all stitched stacks and \
                                 evaluated e1, begin relabeling variables"
                                d);
                          let%bind r2 =
                            Set.fold r1 ~init:(return empty_res)
                              ~f:(fun acc a ->
                                debug (fun m ->
                                    m "r1 length: %d" (Set.length r1));
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
                                      let%bind r0' =
                                        analyze_aux d
                                          (Var (Ident x, l1))
                                          sigma1 pi
                                      in
                                      let%bind acc' = acc in
                                      return (Set.union acc' r0'))
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
                info (fun m -> m "Evaluating: %a" Interp.Pp.pp_expr e_false);
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
            let bool_tf_res =
              Set.of_list (module Res_key) [ BoolAtom true; BoolAtom false ]
            in
            return
              (match expr with
              | Plus _ -> (
                  match (unwrap_res r1, unwrap_res r2) with
                  | [ IntAtom i1 ], [ IntAtom i2 ] ->
                      single_res (IntAtom (i1 + i2))
                  | _ -> single_res IntAnyAtom)
              | Minus _ -> single_res IntAnyAtom
              | Mult _ -> (
                  match (unwrap_res r1, unwrap_res r2) with
                  | [ IntAtom i1 ], [ IntAtom i2 ] ->
                      single_res (IntAtom (i1 * i2))
                  | r1', r2' -> single_res IntAnyAtom)
              | And _ -> (
                  match (unwrap_res r1, unwrap_res r2) with
                  | [ BoolAtom b1 ], [ BoolAtom b2 ] ->
                      single_res (BoolAtom (b1 && b2))
                  | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b2 ] ->
                      let b1 = b11 && b2 in
                      let b2 = b12 && b2 in
                      single_res (BoolAtom (b1 || b2))
                  | [ BoolAtom b1 ], [ BoolAtom b21; BoolAtom b22 ] ->
                      let b1 = b1 && b21 in
                      let b2 = b1 && b22 in
                      single_res (BoolAtom (b1 || b2))
                  | ( [ BoolAtom b11; BoolAtom b12 ],
                      [ BoolAtom b21; BoolAtom b22 ] ) ->
                      let b1 = (b11 && b21) || (b11 && b22) in
                      let b2 = (b12 && b21) || (b12 && b22) in
                      single_res (BoolAtom (b1 || b2))
                  | _ -> bool_tf_res)
              | Or _ -> (
                  match (unwrap_res r1, unwrap_res r2) with
                  | [ BoolAtom b1 ], [ BoolAtom b2 ] ->
                      single_res (BoolAtom (b1 || b2))
                  | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b2 ] ->
                      let b1 = b11 || b2 in
                      let b2 = b12 || b2 in
                      single_res (BoolAtom (b1 || b2))
                  | [ BoolAtom b1 ], [ BoolAtom b21; BoolAtom b22 ] ->
                      let b1 = b1 || b21 in
                      let b2 = b1 || b22 in
                      single_res (BoolAtom (b1 || b2))
                  | ( [ BoolAtom b11; BoolAtom b12 ],
                      [ BoolAtom b21; BoolAtom b22 ] ) ->
                      let b1 = (b11 || b21) || b11 || b22 in
                      let b2 = (b12 || b21) || b12 || b22 in
                      single_res (BoolAtom (b1 || b2))
                  | _ -> bool_tf_res)
              | Equal _ | Ge _ | Gt _ | Le _ | Lt _ -> bool_tf_res
              | _ ->
                  Format.printf "%a\n" pp_expr expr;
                  raise Unreachable [@coverage off])
        | Not e ->
            let%bind r = analyze_aux d e sigma pi in
            return
              (match unwrap_res r with
              | [] -> empty_res
              | [ BoolAtom b ] -> single_res (BoolAtom (not b))
              | _ ->
                  Set.of_list (module Res_key) [ BoolAtom true; BoolAtom false ])
        | Record es ->
            if List.is_empty es then return (single_res (RecAtom []))
            else
              es
              |> List.fold ~init:(return []) ~f:(fun acc (id, ei) ->
                     let%bind acc = acc in
                     let%bind p = analyze_aux d ei sigma pi in
                     return ((id, p) :: acc))
              |> fun rs ->
              let%bind rs = rs in
              return (single_res (RecAtom rs))
        | Projection (e, Ident key) ->
            debug (fun m -> m "[Level %d] === Projection ===" d);
            let%bind r0 = analyze_aux d e sigma pi in
            return (single_res (ProjAtom (r0, Ident key)))
        | Inspection (Ident key, e) ->
            let%bind r0 = analyze_aux d e sigma pi in
            return (single_res (InspAtom (Ident key, r0)))
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
  let r, { vids; sids; freqs; _ } =
    analyze_aux 0 e [] None
      {
        s = Set.empty (module S_key);
        v = Set.empty (module V_key);
        c = Map.empty (module Cache_key);
        vids = Map.empty (module V);
        sids = Map.empty (module S);
        cnt = 0;
        freqs = Map.empty (module Freq_key);
      }
  in

  (* print_freqs freqs;
     Format.printf "vids:\n";
     print_vids vids ~size:false;
     Format.printf "sids:\n";
     print_sids sids ~size:false; *)

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
