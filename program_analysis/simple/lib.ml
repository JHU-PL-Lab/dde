open Core
open Logs
open Option.Let_syntax
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

let log_v_set = Set.iter ~f:(fun st -> debug (fun m -> m "%s" (NewSt.show st)))

let fold_res_app ~init ~f l sigma d =
  List.fold ~init ~f:(fun ((acc_r, acc_s) as acc) a ->
      debug (fun m ->
          m "[Level %d] [Appl] Evaluating 1 possible function being applied:" d);
      debug (fun m -> m "%a" pp_atom a);
      match a with
      | FunAtom (Function (_, e1, _), _, _) -> f acc e1
      | _ -> (acc_r, acc_s))

let fold_res_var ~init ~f expr sigma d r =
  List.fold r ~init ~f:(fun ((acc_r, acc_s) as acc) a ->
      debug (fun m -> m "r1 length: %d" (List.length r));
      debug (fun m -> m "[Level %d] Visiting 1 possible function for e1:" d);
      debug (fun m -> m "%a" pp_atom a);
      match a with
      | FunAtom (Function (Ident x1, _, l1), _, sigma1) -> f acc x1 l1 sigma1
      | _ -> (acc_r, acc_s))

let elim_stub r label =
  if exists_stub r label then
    (* Format.printf "elim_stub: %a\n" pp_res r; *)
    (* Format.printf "label: %a\n" St.pp label; *)
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
                    | None ->
                        []
                        (* Format.printf "base: %a\n" pp_atom base;
                           raise Runtime_error *))
                | _ -> raise Runtime_error)
        (* fun x -> x | stub *)
        | EStubAtom st when St.(label = Estate st) -> []
        | a ->
            (* Format.printf "%a\n" pp_atom a; *)
            [ a ])
    in
    (* Format.printf "result: %a\n" pp_res r'; *)
    r'
  else r

let rec analyze_aux_step d expr sigma pi s v v' =
  if d > !max_d then max_d := d;
  debug_plain "Began recursive call to execution";
  debug (fun m -> m "Max depth so far is: %d" !max_d);
  debug (fun m -> m "expr: %a" Interp.Pp.pp_expr expr);
  debug (fun m -> m "sigma: %s" (show_sigma sigma));
  let r, s' =
    match expr with
    | Int i -> ([ IntAnyAtom ], s)
    | Bool b -> ([ BoolAtom b ], s)
    | Function (_, _, l) -> ([ FunAtom (expr, l, sigma) ], s)
    | Appl (e, _, l) ->
        let d = d + 1 in
        info (fun m ->
            m "[Level %d] === Appl (%a) ====" d Interp.Pp.pp_expr expr);
        (* debug (fun m -> m "%a" Interp.Ast.pp_expr expr); *)
        debug (fun m -> m "sigma: %s" (show_sigma sigma));
        let cycle_label = (l, sigma) in
        let sigma' = l :: sigma in
        let pruned_sigma' = prune_sigma sigma' in
        debug (fun m -> m "sigma_pruned': %s" (show_sigma pruned_sigma'));
        let st = (l, sigma, s) in
        let st' = (l, sigma) in
        (* let st = (l, pruned_sigma', s) in *)
        let lst = NewSt.Lstate st in
        let lst' = St.Lstate st' in
        (* debug (fun m -> m "State: %s" (NewSt.show lst)); *)
        (* debug_plain "v_set:";
           log_v_set v; *)
        (* TODO: try two-pass mechanism again *)
        if Set.mem v lst then (
          debug_plain "Stubbed";
          (* Format.printf "Stubbed\n"; *)
          (* debug (fun m ->
              m "sigma: %s | take: %s" (show_sigma sigma)
                (show_sigma (sigma))); *)
          info (fun m ->
              m "[Level %d] *** Appl (%a) ****" d Interp.Pp.pp_expr expr);
          ([ LStubAtom cycle_label ], s))
        else (
          (* Application *)
          debug_plain "Didn't stub";
          debug (fun m ->
              m "Evaluating function being applied: %a" Interp.Pp.pp_expr e);
          debug (fun m ->
              m "Evaluating function being applied: %a" Interp.Ast.pp_expr e);
          let new_v = Set.add v lst in
          let new_v' = Set.add v' lst' in
          (* we don't remember whatever this subtree visited *)
          let r1, s1 = analyze_aux_step d e sigma pi s new_v new_v' in
          (* let r1 = simplify r1 in *)
          debug (fun m -> m "r1 length: %d" (List.length r1));
          let new_s = Set.add s1 pruned_sigma' in
          let r2, s2 =
            fold_res_app ~init:(choice_empty, new_s) l sigma d r1
              ~f:(fun (acc_r, acc_s) e1 ->
                debug (fun m ->
                    m "[Appl] Evaluating body of function being applied: %a"
                      Interp.Pp.pp_expr e1);
                let ri, si =
                  analyze_aux_step d e1 pruned_sigma' pi new_s new_v new_v'
                in
                (List.fold ri ~init:acc_r ~f:Set.add, Set.union acc_s si))
          in
          let r2 = Set.elements r2 in
          debug (fun m -> m "r2: %a" pp_res r2);
          let r2 = elim_stub r2 (St.Lstate cycle_label) in
          info (fun m ->
              m "[Level %d] *** Appl (%a) ****" d Interp.Pp.pp_expr expr);
          (r2, s2))
    | Var (Ident x, l) ->
        let d = d + 1 in
        info (fun m -> m "[Level %d] === Var (%s, %d) ====" d x l);
        let cycle_label = (expr, sigma) in
        let st = (expr, sigma, s) in
        let st' = (expr, sigma) in
        let est = NewSt.Estate st in
        let est' = St.Estate st' in
        let new_v = Set.add v est in
        let new_v' = Set.add v' est' in
        (* debug (fun m -> m "State: %s" (Grammar.NewSt.show est)); *)
        (* debug_plain "v_set:";
           log_v_set v; *)
        if Set.mem v est then (
          (* Var Stub *)
          debug (fun m -> m "Stubbed: %s" x);
          (* Format.printf "Stubbed: %s\n" x; *)
          info (fun m -> m "[Level %d] *** Var (%s, %d) ****" d x l);
          ([ EStubAtom cycle_label ], s))
        else (
          debug_plain "Didn't stub";
          match get_myfun l with
          | Some (Function (Ident x1, _, l_myfun)) ->
              if String.(x = x1) then (
                (* Var Local *)
                info (fun m -> m "[Level %d] === Var Local (%s, %d) ====" d x l);
                debug (fun m -> m "sigma: %s" (show_sigma sigma));
                let s_hd, s_tl = (List.hd_exn sigma, List.tl_exn sigma) in
                match get_myexpr s_hd with
                | Appl (_, e2, l') ->
                    let r1, s1 =
                      debug_plain "Begin stitching stacks";
                      (* debug_plain "S set:";
                         debug (fun m -> m "%s" (show_set s));
                         debug (fun m ->
                             m "Head of candidate fragments must be: %d" l');
                         debug (fun m ->
                             m
                               "Tail of candidate fragments must start with: \
                                %s"
                               (show_sigma s_tl)); *)
                      (* enumerate all matching stacks in the set *)
                      Set.fold s ~init:(choice_empty, s)
                        ~f:(fun (acc_r, acc_s) sigma_i ->
                          let sigma_i_hd, sigma_i_tl =
                            (List.hd_exn sigma_i, List.tl_exn sigma_i)
                          in
                          (* the fact that we can prune away "bad" stacks like this
                             makes DDE for program analysis superior *)
                          if sigma_i_hd = l' && starts_with sigma_i_tl s_tl then (
                            debug (fun m ->
                                m
                                  "[Level %d] Stitched! Evaluating Appl \
                                   argument, using stitched stack %s:"
                                  d (show_sigma sigma_i_tl));
                            debug (fun m -> m "%a" Interp.Pp.pp_expr e2);
                            (* debug (fun m ->
                                m "%a" Interp.Ast.pp_expr e2); *)
                            (* stitch the stack to gain more precision *)
                            let ri, si =
                              analyze_aux_step d e2 sigma_i_tl pi s new_v new_v'
                            in
                            ( List.fold ri ~init:acc_r ~f:Set.add,
                              Set.union acc_s si ))
                          else (acc_r, acc_s))
                    in
                    info (fun m ->
                        m "[Level %d] *** Var Local (%s, %d) ****" d x l);
                    info (fun m -> m "[Level %d] *** Var (%s, %d) ****" d x l);
                    let r1 = Set.elements r1 in
                    debug (fun m -> m "r1: %a" pp_res r1);
                    let r1 = elim_stub r1 (St.Estate cycle_label) in
                    (r1, s1)
                | _ -> raise Unreachable [@coverage off])
              else (
                (* Var Non-Local *)
                info (fun m ->
                    m "[Level %d] === Var Non-Local (%s, %d) ====" d x l);
                debug (fun m -> m "sigma: %s" (show_sigma sigma));
                debug_plain "Reading Appl at front of sigma";
                match get_myexpr (List.hd_exn sigma) with
                | Appl (e1, _, l2) ->
                    debug_plain "[Var Non-Local] Didn't stub e1";
                    debug_plain "Function being applied at front of sigma:";
                    debug (fun m -> m "%a" Interp.Pp.pp_expr e1);
                    debug (fun m -> m "%a" Interp.Ast.pp_expr e1);
                    let s_tl = List.tl_exn sigma in
                    debug_plain "Begin stitching stacks";
                    (* debug_plain "S set:";
                       debug (fun m -> m "%s" (show_set s));
                       debug (fun m ->
                           m "Head of candidate fragments must be: %d" l2);
                       debug (fun m ->
                           m "Tail of candidate fragments must start with: %s"
                             (show_sigma s_tl)); *)
                    (* enumerate all matching stacks in the set *)
                    let r1, s1 =
                      Set.fold s ~init:(choice_empty, s)
                        ~f:(fun (acc_r, acc_s) si ->
                          let si_hd, si_tl = (List.hd_exn si, List.tl_exn si) in
                          if Stdlib.(si_hd = l2) && starts_with si_tl s_tl then (
                            debug (fun m ->
                                m
                                  "[Level %d] Stitched! Evaluating function \
                                   being applied at front of sigma, using \
                                   stitched stack %s"
                                  d (show_sigma si_tl));
                            (* stitch the stack to gain more precision *)
                            (* let new_v =
                                 Set.add v (NewSt.Estate (e1, si_tl, s))
                               in *)
                            let r0, s0 =
                              analyze_aux_step d e1 si_tl pi s v v'
                            in
                            ( List.fold r0 ~init:acc_r ~f:Set.add,
                              Set.union acc_s s0 ))
                          else (acc_r, acc_s))
                    in
                    let r1 = Set.elements r1 in
                    (* let r1 = simplify r1 in *)
                    (* let new_st = (expr, sigma, s1) in
                       let new_v = Set.add v (NewSt.Estate new_st) in *)
                    debug_plain
                      "Found all stitched stacks and evaluated e1, begin \
                       relabeling variables";
                    let r2, s2 =
                      fold_res_var ~init:(choice_empty, s1) expr sigma d r1
                        ~f:(fun (acc_r, acc_s) x1' l1 sigma1 ->
                          if Stdlib.(x1 = x1') && l_myfun = l1 then (
                            debug (fun m ->
                                m
                                  "[Var Non-Local] Relabel %s with label %d \
                                   and evaluate"
                                  x l1);
                            let r0', s0' =
                              analyze_aux_step d
                                (Var (Ident x, l1))
                                sigma1 pi s1 new_v new_v'
                            in
                            ( List.fold r0' ~init:acc_r ~f:Set.add,
                              Set.union acc_s s0' ))
                          else (acc_r, acc_s))
                    in
                    info (fun m ->
                        m "[Level %d] *** Var Non-Local (%s, %d) ****" d x l);
                    info (fun m -> m "[Level %d] *** Var (%s, %d) ****" d x l);
                    let r2 = Set.elements r2 in
                    debug (fun m -> m "r2: %a" pp_res r2);
                    let r2 = elim_stub r2 (St.Estate cycle_label) in
                    (r2, s2)
                | _ -> raise Unreachable [@coverage off])
          | _ -> raise Unreachable [@coverage off])
    | If (e, e_true, e_false, l) -> (
        debug (fun m -> m "[Level %d] === If ===" d);
        let d = d + 1 in
        let r_cond, s_cond = analyze_aux_step d e sigma None s v v' in
        (* TODO: why do I need the following line? *)
        (* let r_cond = simplify r_cond in *)
        (* Format.printf "r_cond: %a\n" pp_res r_cond; *)
        match r_cond with
        (* TODO *)
        | [ BoolAtom b ] ->
            debug (fun m -> m "[Level %d] === If %b ===" d b);
            if b then (
              let r_true, s_true =
                analyze_aux_step d e_true sigma None s v v'
              in
              debug (fun m -> m "[Level %d] *** If %b ***" d b);
              (r_true, Set.union s_cond s_true))
            else
              let r_false, s_false =
                analyze_aux_step d e_false sigma None s v v'
              in
              debug (fun m -> m "[Level %d] *** If %b ***" d b);
              (r_false, Set.union s_cond s_false)
        | _ ->
            debug (fun m -> m "[Level %d] === If Both ===" d);
            (* Format.printf "r_cond: %a\n" pp_res r_cond; *)
            let r_true, s_true = analyze_aux_step d e_true sigma None s v v' in
            info (fun m -> m "Evaluating: %a" Interp.Pp.pp_expr e_false);
            let r_false, s_false =
              analyze_aux_step d e_false sigma None s v v'
            in
            debug (fun m -> m "[Level %d] *** If Both ***" d);
            (r_true @ r_false, Set.union s (Set.union s_true s_false)))
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
        let d = d + 1 in
        info (fun m ->
            m "[Level %d] === Binop (%a) ====" d Interp.Pp.pp_expr expr);
        (* Format.printf "e1: %a | e2: %a\n" pp_expr e1 pp_expr e2; *)
        let r1, s1 = analyze_aux_step d e1 sigma pi s v v' in
        let r2, s2 = analyze_aux_step d e2 sigma pi s1 v v' in
        debug (fun m ->
            m "[Level %d] Evaluated binop to (%a <op> %a)" d Utils.pp_res r1
              Utils.pp_res r2);
        debug (fun m ->
            m "[Level %d] Evaluated binop to (%a <op> %a)" d Grammar.pp_res r1
              Grammar.pp_res r2);
        info (fun m ->
            m "[Level %d] *** Binop (%a) ****" d Interp.Pp.pp_expr expr);
        ( (match expr with
          | Plus _ -> (
              match (r1, r2) with
              | [ IntAtom i1 ], [ IntAtom i2 ] -> [ IntAtom (i1 + i2) ]
              | _ ->
                  (* Format.printf "Plus: r1: %a | r2: %a\n" pp_res r1 pp_res
                     r2; *)
                  [ IntAnyAtom ])
          | Minus _ -> [ IntAnyAtom ]
          | Mult _ -> (
              match (r1, r2) with
              | [ IntAtom i1 ], [ IntAtom i2 ] -> [ IntAtom (i1 * i2) ]
              | r1', r2' -> [ IntAnyAtom ])
          | And _ -> (
              match (r1, r2) with
              | [ BoolAtom b1 ], [ BoolAtom b2 ] -> [ BoolAtom (b1 && b2) ]
              | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b2 ] ->
                  let b1 = b11 && b2 in
                  let b2 = b12 && b2 in
                  [ BoolAtom (b1 || b2) ]
              | [ BoolAtom b1 ], [ BoolAtom b21; BoolAtom b22 ] ->
                  let b1 = b1 && b21 in
                  let b2 = b1 && b22 in
                  [ BoolAtom (b1 || b2) ]
              | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b21; BoolAtom b22 ]
                ->
                  let b1 = (b11 && b21) || (b11 && b22) in
                  let b2 = (b12 && b21) || (b12 && b22) in
                  [ BoolAtom (b1 || b2) ]
              | _ ->
                  (* Format.printf "r1: %a | r2: %a\n" pp_res r1 pp_res r2; *)
                  [ BoolAtom true; BoolAtom false ])
          | Or _ -> (
              match (r1, r2) with
              | [ BoolAtom b1 ], [ BoolAtom b2 ] -> [ BoolAtom (b1 || b2) ]
              | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b2 ] ->
                  let b1 = b11 || b2 in
                  let b2 = b12 || b2 in
                  [ BoolAtom (b1 || b2) ]
              | [ BoolAtom b1 ], [ BoolAtom b21; BoolAtom b22 ] ->
                  let b1 = b1 || b21 in
                  let b2 = b1 || b22 in
                  [ BoolAtom (b1 || b2) ]
              | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b21; BoolAtom b22 ]
                ->
                  let b1 = (b11 || b21) || b11 || b22 in
                  let b2 = (b12 || b21) || b12 || b22 in
                  [ BoolAtom (b1 || b2) ]
              | _ ->
                  (* Format.printf "r1: %a | r2: %a\n" pp_res r1 pp_res r2; *)
                  [ BoolAtom true; BoolAtom false ])
          | Equal _ | Ge _ | Gt _ | Le _ | Lt _ ->
              [ BoolAtom true; BoolAtom false ]
          | _ ->
              Format.printf "%a\n" pp_expr expr;
              raise Unreachable [@coverage off]),
          Set.union s (Set.union s1 s2) )
    | Not e -> (
        let d = d + 1 in
        let r, s = analyze_aux_step d e sigma pi s v v' in
        match r with
        | [ BoolAtom b ] ->
            (* Format.printf "%a\n" pp_res r; *)
            ([ BoolAtom (not b) ], s)
        | [] -> ([], s)
        | _ -> ([ BoolAtom false; BoolAtom true ], s))
    | Record entries ->
        let d = d + 1 in
        ( [
            RecAtom
              (entries
              |> List.map ~f:(fun (x, ei) ->
                     ( x,
                       let r, _ = analyze_aux_step d ei sigma pi s v v' in
                       r )));
          ],
          s )
    | Projection (e, Ident key) ->
        debug (fun m -> m "[Level %d] === Projection ===" d);
        let d = d + 1 in
        let r0, s0 = analyze_aux_step d e sigma pi s v v' in
        ([ ProjAtom (r0, Ident key) ], s0)
    | Inspection (Ident key, e) ->
        let d = d + 1 in
        let r0, s0 = analyze_aux_step d e sigma pi s v v' in
        ([ InspAtom (Ident key, r0) ], s0)
    | LetAssert (id, e1, e2) ->
        let d = d + 1 in
        let r1, s1 = analyze_aux_step d e1 sigma pi s v v' in
        let r2 = eval_assert e2 id in
        ([ AssertAtom (id, r1, r2) ], s1)
    | Let _ -> raise Unreachable [@coverage off]
  in
  (simplify r, s')
(* (r, s') *)
(* TODO: run with poor man's cache first then use S to rerun *)

let analyze ?(debug_mode = false) ?(verify = true) ?(test_num = 0)
    ?(should_cache = true) e =
  is_debug_mode := debug_mode;

  let e = transform_let e in
  build_myfun e None;
  debug (fun m -> m "%a" Interp.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  (* Format.printf "%a\n" pp_expr e; *)
  let r, s =
    analyze_aux_step 0 e [] None
      (Set.empty (module SKey))
      (Set.empty (module NewSt))
      (Set.empty (module St))
  in

  (* let r = simplify r in *)
  (* dot_of_result test_num r; *)
  debug (fun m -> m "Result: %a" Utils.pp_res r);
  debug (fun m -> m "Result: %a" Grammar.pp_res r);
  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" @@ show_expr e;
     Format.printf "****** Label Table ******\n";
     Interp.Lib.print_myexpr myexpr;
     Format.printf "****** Label Table ******\n\n"))
  [@coverage off];

  clean_up ();

  (* if verify then verify_result r; *)
  r
