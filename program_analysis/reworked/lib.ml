open Core
open Logs
open Option.Let_syntax
open Interpreter.Ast
open Grammar
open Utils
open Solver
open Simplifier

exception Unreachable
exception BadAssert
exception Runtime_error

let empty_choice_set = Set.empty (module Choice)

(* controls whether to generate logs:
   "logs" in _build/default/program_analysis/tests *)
let gen_logs = ref false
let debug_plain msg = if !gen_logs then debug (fun m -> m msg)
let debug msg = if !gen_logs then debug msg
let info_plain msg = if !gen_logs then info msg
let info msg = if !gen_logs then info msg

(* maximum recursion depth ever reached by execution so far *)
let max_d = ref 0

(* let solve_cond ?(v = Set.empty (module NewSt)) r b =
   (* let solver = Z3.Solver.mk_solver_s ctx "HORN" in *)
   Solver.chcs_of_res r v;
   let p = Option.value_exn !Solver.entry_decl in
   let chcs = Hash_set.to_list Solver.chcs in
   let rb = zconst "r" bsort in
   let manual = [ rb ] |. (p <-- [ rb ]) --> (rb === zbool b) in
   let chcs = manual :: chcs in
   Z3.Solver.add solver chcs;

   (* if b then (
      (* Format.printf "CHCs:\n";
         List.iter chcs ~f:(fun chc -> Format.printf "%s\n" (Z3.Expr.to_string chc)); *)
      debug_plain "CHCs:";
      List.iter chcs ~f:(fun chc ->
          debug (fun m -> m "%s" (Z3.Expr.to_string chc)))); *)

   (* let start = Stdlib.Sys.time () in *)
   let status = Z3.Solver.check solver [] in
   (* Format.printf "cond execution time: %f\n" (Stdlib.Sys.time () -. start); *)
   let sat =
     match status with
     | SATISFIABLE ->
         (* let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
            model |> Z3.Model.to_string |> Format.printf "Model:\n%s\n\n"; *)
         (* Format.printf "sat\n"; *)
         (* solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s"; *)
         (* let prog = Format.asprintf "%a" pp_res r in
            Format.printf "if condition: %s\n" prog; *)
         true
     | UNSATISFIABLE -> false
     | UNKNOWN -> false
   in
   (* let start = Stdlib.Sys.time () in *)
   Solver.reset ();
   (* Format.printf "reset execution time: %f\n" (Stdlib.Sys.time () -. start); *)
   (* Format.print_flush (); *)
   sat *)

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
      | Projection (e1, x) -> failwith "Not supported"
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

let log_v_set = Set.iter ~f:(fun st -> debug (fun m -> m "%s" (NewSt.show st)))

let rec fold_res_app ~init ~f l sigma d =
  List.fold ~init ~f:(fun ((acc_r, acc_s) as acc) a ->
      debug (fun m ->
          m "[Level %d] [Appl] Evaluating 1 possible function being applied:" d);
      debug (fun m -> m "%a" pp_atom a);
      (* debug (fun m -> m "%a" Grammar.pp_atom a); *)
      match a with
      | FunAtom (Function (_, e1, _), _, _) -> f acc e1
      | _ ->
          debug (fun m -> m "Not a function, skipping: %a" pp_atom a);
          (acc_r, acc_s))

let rec fold_res_var ~init ~f expr sigma d r =
  List.fold r ~init ~f:(fun ((acc_r, acc_s) as acc) a ->
      debug (fun m -> m "r1 length: %d" (List.length r));
      debug (fun m -> m "[Level %d] Visiting 1 possible function for e1:" d);
      debug (fun m -> m "%a" pp_atom a);
      (* debug (fun m -> m "%a" Grammar.pp_atom a); *)
      match a with
      | FunAtom (Function (Ident x1, _, l1), _, sigma1) -> f acc x1 l1 sigma1
      | _ ->
          debug (fun m -> m "Not a function, skipping: %a" pp_atom a);
          (acc_r, acc_s))

let rec exists_stub r label =
  List.exists r ~f:(function
    | FunAtom _ | IntAllAtom | IntAtom _ | BoolAtom _ -> false
    | LabelStubAtom st -> St.(label = St.Lstate st)
    | ExprStubAtom st -> St.(label = St.Estate st)
    | RecordAtom entries ->
        List.exists entries ~f:(fun (_, r) -> exists_stub r label)
    | ProjectionAtom (r, _) | InspectionAtom (_, r) -> exists_stub r label
    | _ as a ->
        Format.printf "%a" pp_atom a;
        failwith "unimplemented")

let elim_stub r label =
  if exists_stub r label then (
    Format.printf "elim_stub: %a\n" pp_res r;
    (* Format.printf "label: %a\n" St.pp label; *)
    let bases =
      List.filter_map r ~f:(fun a ->
          match a with
          | RecordAtom _ -> Some a
          | ProjectionAtom (([ RecordAtom es ] as r), Ident key)
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
        | ProjectionAtom ([ ExprStubAtom st ], Ident key)
          when St.(label = Estate st) ->
            List.concat_map bases ~f:(fun base ->
                match base with
                | RecordAtom es -> (
                    match
                      List.find es ~f:(fun (Ident key', _) ->
                          String.(key = key'))
                    with
                    | Some (_, r) -> r
                    | None -> raise Runtime_error)
                | _ -> raise Runtime_error)
        (* fun x -> x | stub *)
        | ExprStubAtom st when St.(label = Estate st) -> []
        | a ->
            (* Format.printf "%a\n" pp_atom a; *)
            [ a ])
    in
    Format.printf "result: %a\n" pp_res r';
    r')
  else r

(* let cache = Hashtbl.create (module Cache_key) *)

let rec analyze_aux_step d expr sigma pi s v =
  if d > !max_d then max_d := d;
  debug_plain "Began recursive call to execution";
  debug (fun m -> m "Max depth so far is: %d" !max_d);
  debug (fun m -> m "expr: %a" Interpreter.Pp.pp_expr expr);
  debug (fun m -> m "sigma: %s" (show_sigma sigma));
  (* let cache_key = (expr, sigma) in *)
  (* let cache_key = (expr, sigma, Set.length v) in
  match Hashtbl.find cache cache_key with
  | Some r ->
      debug (fun m -> m "Cache hit: %a" pp_res r);
      if List.length r = 0 then Format.printf "wtf\n";
      (* debug (fun m -> m "cache hit: %a" Grammar.pp_res r); *)
      (* debug_plain "Cache:";
         Hashtbl.iteri cache ~f:(fun ~key:(e, sigma) ~data ->
             debug (fun m ->
                 m "(%a, %s) -> %a" Interpreter.Pp.pp_expr e (show_sigma sigma)
                   pp_res data)); *)
      (r, s)
  | _ -> *)
      let r, s' =
        match expr with
        | Int i -> ([ IntAtom i ], s)
        | Bool b -> ([ BoolAtom b ], s)
        | Function (_, _, l) -> ([ FunAtom (expr, l, sigma) ], s)
        | Appl (e, _, l) ->
            let d = d + 1 in
            info (fun m ->
                m "[Level %d] =========== Appl (%a) ============" d
                  Interpreter.Pp.pp_expr expr);
            (* debug (fun m -> m "%a" Interpreter.Ast.pp_expr expr); *)
            debug (fun m -> m "sigma: %s" (show_sigma sigma));
            let cycle_label = (l, sigma) in
            let sigma' = l :: sigma in
            let pruned_sigma' = prune_sigma sigma' in
            debug (fun m -> m "sigma_pruned': %s" (show_sigma pruned_sigma'));
            let st = (l, sigma, s) in
            (* let st = (l, pruned_sigma', s) in *)
            let lst = NewSt.Lstate st in
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
                  m "[Level %d] *********** Appl (%a) ************" d
                    Interpreter.Pp.pp_expr expr);
              ([ LabelStubAtom cycle_label ], s))
            else (
              (* Application *)
              debug_plain "Didn't stub";
              debug (fun m ->
                  m "Evaluating function being applied: %a"
                    Interpreter.Pp.pp_expr e);
              debug (fun m ->
                  m "Evaluating function being applied: %a"
                    Interpreter.Ast.pp_expr e);
              let new_v = Set.add v lst in
              (* we don't remember whatever this subtree visited *)
              let r1, s1 = analyze_aux_step d e sigma pi s new_v in
              (* let r1 = simplify r1 in *)
              debug (fun m -> m "r1 length: %d" (List.length r1));
              let new_s = Set.add s1 pruned_sigma' in
              let r2, s2 =
                fold_res_app ~init:(empty_choice_set, new_s) l sigma d r1
                  ~f:(fun (acc_r, acc_s) e1 ->
                    debug (fun m ->
                        m "[Appl] Evaluating body of function being applied: %a"
                          Interpreter.Pp.pp_expr e1);
                    let ri, si =
                      analyze_aux_step d e1 pruned_sigma' pi new_s new_v
                    in
                    (List.fold ri ~init:acc_r ~f:Set.add, Set.union acc_s si))
              in
              let r2 = Set.elements r2 in
              debug (fun m -> m "r2: %a" pp_res r2);
              (* add_cycle r2 (St.Lstate cycle_label); *)
              let r2 = elim_stub r2 (St.Lstate cycle_label) in
              info (fun m ->
                  m "[Level %d] *********** Appl (%a) ************" d
                    Interpreter.Pp.pp_expr expr);
              (r2, s2))
        | Var (Ident x, l) ->
            let d = d + 1 in
            info (fun m ->
                m "[Level %d] =========== Var (%s, %d) ============" d x l);
            let cycle_label = (expr, sigma) in
            let st = (expr, sigma, s) in
            let est = NewSt.Estate st in
            (* debug (fun m -> m "State: %s" (Grammar.NewSt.show est)); *)
            (* debug_plain "v_set:";
               log_v_set v; *)
            if Set.mem v est then (
              (* Var Stub *)
              debug (fun m -> m "Stubbed: %s" x);
              (* Format.printf "Stubbed: %s\n" x; *)
              info (fun m ->
                  m "[Level %d] *********** Var (%s, %d) ************" d x l);
              ([ ExprStubAtom cycle_label ], s))
            else (
              debug_plain "Didn't stub";
              match get_myfun l with
              | Some (Function (Ident x1, _, l_myfun)) ->
                  if String.(x = x1) then (
                    (* Var Local *)
                    info (fun m ->
                        m
                          "[Level %d] =========== Var Local (%s, %d) \
                           ============"
                          d x l);
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
                          let new_v = Set.add v est in
                          (* enumerate all matching stacks in the set *)
                          Set.fold s ~init:(empty_choice_set, s)
                            ~f:(fun (acc_r, acc_s) sigma_i ->
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
                                       argument, using stitched stack %s:"
                                      d (show_sigma sigma_i_tl));
                                debug (fun m ->
                                    m "%a" Interpreter.Pp.pp_expr e2);
                                (* debug (fun m ->
                                    m "%a" Interpreter.Ast.pp_expr e2); *)
                                (* stitch the stack to gain more precision *)
                                let ri, si =
                                  analyze_aux_step d e2 sigma_i_tl pi s new_v
                                in
                                ( List.fold ri ~init:acc_r ~f:Set.add,
                                  Set.union acc_s si ))
                              else (acc_r, acc_s))
                        in
                        info (fun m ->
                            m
                              "[Level %d] *********** Var Local (%s, %d) \
                               ************"
                              d x l);
                        info (fun m ->
                            m "[Level %d] *********** Var (%s, %d) ************"
                              d x l);
                        let r1 = Set.elements r1 in
                        debug (fun m -> m "r1: %a" pp_res r1);
                        (* add_cycle r1 (St.Estate cycle_label); *)
                        let r1 = elim_stub r1 (St.Estate cycle_label) in
                        (r1, s1)
                    | _ -> raise Unreachable [@coverage off])
                  else (
                    (* Var Non-Local *)
                    info (fun m ->
                        m
                          "[Level %d] =========== Var Non-Local (%s, %d) \
                           ============"
                          d x l);
                    debug (fun m -> m "sigma: %s" (show_sigma sigma));
                    debug_plain "Reading Appl at front of sigma";
                    match get_myexpr (List.hd_exn sigma) with
                    | Appl (e1, _, l2) ->
                        debug_plain "[Var Non-Local] Didn't stub e1";
                        debug_plain "Function being applied at front of sigma:";
                        debug (fun m -> m "%a" Interpreter.Pp.pp_expr e1);
                        debug (fun m -> m "%a" Interpreter.Ast.pp_expr e1);
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
                          Set.fold s ~init:(empty_choice_set, s)
                            ~f:(fun (acc_r, acc_s) si ->
                              let si_hd, si_tl =
                                (List.hd_exn si, List.tl_exn si)
                              in
                              if Stdlib.(si_hd = l2) && starts_with si_tl s_tl
                              then (
                                debug (fun m ->
                                    m
                                      "[Level %d] Stitched! Evaluating \
                                       function being applied at front of \
                                       sigma, using stitched stack %s"
                                      d (show_sigma si_tl));
                                (* stitch the stack to gain more precision *)
                                (* let new_v =
                                     Set.add v (NewSt.Estate (e1, si_tl, s))
                                   in *)
                                let r0, s0 =
                                  analyze_aux_step d e1 si_tl pi s v
                                in
                                ( List.fold r0 ~init:acc_r ~f:Set.add,
                                  Set.union acc_s s0 ))
                              else (acc_r, acc_s))
                        in
                        let r1 = Set.elements r1 in
                        (* let r1 = simplify r1 in *)
                        let new_st = (expr, sigma, s1) in
                        let new_v = Set.add v (NewSt.Estate new_st) in
                        debug_plain
                          "Found all stitched stacks and evaluated e1, begin \
                           relabeling variables";
                        let r2, s2 =
                          fold_res_var ~init:(empty_choice_set, s1) expr sigma d
                            r1 ~f:(fun (acc_r, acc_s) x1' l1 sigma1 ->
                              if Stdlib.(x1 = x1') && l_myfun = l1 then (
                                debug (fun m ->
                                    m
                                      "[Var Non-Local] Relabel %s with label \
                                       %d and evaluate"
                                      x l1);
                                let r0', s0' =
                                  analyze_aux_step d
                                    (Var (Ident x, l1))
                                    sigma1 pi s1 new_v
                                in
                                ( List.fold r0' ~init:acc_r ~f:Set.add,
                                  Set.union acc_s s0' ))
                              else (acc_r, acc_s))
                        in
                        info (fun m ->
                            m
                              "[Level %d] *********** Var Non-Local (%s, %d) \
                               ************"
                              d x l);
                        info (fun m ->
                            m "[Level %d] *********** Var (%s, %d) ************"
                              d x l);
                        let r2 = Set.elements r2 in
                        debug (fun m -> m "r2: %a" pp_res r2);
                        (* add_cycle r2 (St.Estate cycle_label); *)
                        let r2 = elim_stub r2 (St.Estate cycle_label) in
                        (r2, s2)
                    | _ -> raise Unreachable [@coverage off])
              | _ -> raise Unreachable [@coverage off])
        | If (e, e_true, e_false, l) -> (
            debug (fun m -> m "[Level %d] =========== If ===========" d);
            let d = d + 1 in
            let r_cond, s_cond = analyze_aux_step d e sigma None s v in
            (* TODO: why do I need the following line? *)
            let r_cond = simplify r_cond in
            (* Format.printf "r_cond: %a\n" pp_res r_cond; *)
            match r_cond with
            (* TODO *)
            | [ BoolAtom b ] ->
                if b then
                  let r_true, s_true =
                    analyze_aux_step d e_true sigma None s v
                  in
                  (r_true, Set.union s_cond s_true)
                else
                  let r_false, s_false =
                    analyze_aux_step d e_false sigma None s v
                  in
                  (r_false, Set.union s_cond s_false)
            (* | [ InspectionAtom _ ] ->
                Hashtbl.iteri cycles ~f:(fun ~key ~data ->
                    Format.printf "%a -> %a\n" St.pp key pp_res data);
                failwith "what" *)
            | _ ->
                (* Format.printf "r_cond: %a\n" pp_res r_cond; *)
                let r_true, s_true = analyze_aux_step d e_true sigma None s v in
                info (fun m ->
                    m "Evaluating: %a" Interpreter.Pp.pp_expr e_false);
                let r_false, s_false =
                  analyze_aux_step d e_false sigma None s v
                in
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
                m "[Level %d] =========== Binop (%a) ============" d
                  Interpreter.Pp.pp_expr expr);
            (* Format.printf "e1: %a | e2: %a\n" pp_expr e1 pp_expr e2; *)
            let r1, s1 = analyze_aux_step d e1 sigma pi s v in
            let r2, s2 = analyze_aux_step d e2 sigma pi s1 v in
            debug (fun m ->
                m "[Level %d] Evaluated binop to (%a <op> %a)" d Utils.pp_res r1
                  Utils.pp_res r2);
            debug (fun m ->
                m "[Level %d] Evaluated binop to (%a <op> %a)" d Grammar.pp_res
                  r1 Grammar.pp_res r2);
            info (fun m ->
                m "[Level %d] *********** Binop (%a) ************" d
                  Interpreter.Pp.pp_expr expr);
            ( (match expr with
              | Plus _ -> (
                  match (r1, r2) with
                  | [ IntAtom i1 ], [ IntAtom i2 ] -> [ IntAtom (i1 + i2) ]
                  | _ ->
                      (* Format.printf "Plus: r1: %a | r2: %a\n" pp_res r1 pp_res r2; *)
                      [ IntAllAtom ])
              | Minus _ -> [ IntAllAtom ]
              | Mult _ -> (
                  match (r1, r2) with
                  | [ IntAtom i1 ], [ IntAtom i2 ] -> [ IntAtom (i1 * i2) ]
                  | r1', r2' -> [ IntAllAtom ])
              | And _ -> (
                  match (r1, r2) with
                  | [ BoolAtom b1 ], [ BoolAtom b2 ] ->
                      (* Format.printf "yo\n"; *)
                      [ BoolAtom (b1 && b2) ]
                  | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b2 ] ->
                      let b1 = b11 && b2 in
                      let b2 = b12 && b2 in
                      [ BoolAtom (b1 || b2) ]
                  | [ BoolAtom b1 ], [ BoolAtom b21; BoolAtom b22 ] ->
                      let b1 = b1 && b21 in
                      let b2 = b1 && b22 in
                      [ BoolAtom (b1 || b2) ]
                  | ( [ BoolAtom b11; BoolAtom b12 ],
                      [ BoolAtom b21; BoolAtom b22 ] ) ->
                      let b1 = (b11 && b21) || (b11 && b22) in
                      let b2 = (b12 && b21) || (b12 && b22) in
                      [ BoolAtom (b1 || b2) ]
                  | _ ->
                      (* Format.printf "r1: %a | r2: %a\n" pp_res r1 pp_res r2; *)
                      [ BoolAtom true; BoolAtom false ])
              | Or _ -> (
                  match (r1, r2) with
                  | [ BoolAtom b1 ], [ BoolAtom b2 ] ->
                      (* Format.printf "ayo\n"; *)
                      [ BoolAtom (b1 || b2) ]
                  | [ BoolAtom b11; BoolAtom b12 ], [ BoolAtom b2 ] ->
                      let b1 = b11 || b2 in
                      let b2 = b12 || b2 in
                      [ BoolAtom (b1 || b2) ]
                  | [ BoolAtom b1 ], [ BoolAtom b21; BoolAtom b22 ] ->
                      let b1 = b1 || b21 in
                      let b2 = b1 || b22 in
                      [ BoolAtom (b1 || b2) ]
                  | ( [ BoolAtom b11; BoolAtom b12 ],
                      [ BoolAtom b21; BoolAtom b22 ] ) ->
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
            let r, s = analyze_aux_step d e sigma pi s v in
            match r with
            | [ BoolAtom b ] ->
                (* Format.printf "%a\n" pp_res r; *)
                ([ BoolAtom (not b) ], s)
            | [] -> ([], s)
            | _ -> ([ BoolAtom false; BoolAtom true ], s))
        | Record entries ->
            let d = d + 1 in
            ( [
                RecordAtom
                  (entries
                  |> List.map ~f:(fun (x, ei) ->
                         ( x,
                           let r, _ = analyze_aux_step d ei sigma pi s v in
                           r )));
              ],
              s )
        | Projection (e, Ident key) ->
            debug (fun m -> m "[Level %d] =========== Projection ===========" d);
            let d = d + 1 in
            let r0, s0 = analyze_aux_step d e sigma pi s v in
            ([ ProjectionAtom (r0, Ident key) ], s0)
        | Inspection (Ident key, e) ->
            let d = d + 1 in
            let r0, s0 = analyze_aux_step d e sigma pi s v in
            ([ InspectionAtom (Ident key, r0) ], s0)
        | LetAssert (id, e1, e2) ->
            let d = d + 1 in
            let r1, s1 = analyze_aux_step d e1 sigma pi s v in
            let r2 = eval_assert e2 id in
            ([ AssertAtom (id, r1, r2) ], s1)
        | Let _ -> raise Unreachable [@coverage off]
      in
      (* Hashtbl.remove cache cache_key;
      Hashtbl.add_exn cache ~key:cache_key ~data:r; *)
      debug (fun m ->
          m "Insert into cache: (%a, %s) -> %a" Interpreter.Pp.pp_expr expr
            (show_sigma sigma) pp_res r);
      (simplify r, s')
(* (r, s') *)

and analyze_aux n e_glob d expr sigma pi s v =
  debug (fun m -> m "[Level %d] [n = %d] Entered analyze_aux" d n);
  let r, s' = analyze_aux_step d expr sigma pi s v in
  debug (fun m -> m "[Level %d] After analyze_aux_step" d);
  if Set.compare_direct s s' = 0 then (
    debug_plain "S didn't change, finishing...";
    (r, s'))
  else (
    debug (fun m -> m "r: %a" pp_res r);
    debug (fun m -> m "[Level %d] [n = %d] Restarting afresh" d n);
    (* debug (fun m ->
        m "[Level %d] S before evaluating e_glob:\n%s" d (show_set s')); *)
    (* Hashtbl.clear cache; *)
    let r, s' =
      analyze_aux (n + 1) e_glob 0 e_glob [] None s' (Set.empty (module NewSt))
    in
    (* debug (fun m ->
        m "[Level %d] S after evaluating e_glob:\n%s" d (show_set s')); *)
    (* (simplify r, s') *)
    (r, s'))

let analyze ?(debug_mode = false) ?(verify = true) ?(test_num = 0) e =
  is_debug_mode := debug_mode;

  let e = transform_let e in
  build_myfun e None;
  debug (fun m -> m "%a" Interpreter.Pp.pp_expr e);
  debug (fun m -> m "%a" pp_expr e);

  (* Format.printf "%a\n" pp_expr e; *)
  (* let r, s =
    analyze_aux 0 e 0 e [] None
      (Set.empty (module SKey))
      (Set.empty (module NewSt))
  in *)
  let r, s =
       analyze_aux_step 0 e [] None
         (Set.empty (module SKey))
         (Set.empty (module NewSt))
     in
  (* let r = simplify r in *)
  (* dot_of_result test_num r; *)
  debug (fun m -> m "Result: %a" Utils.pp_res r);
  debug (fun m -> m "Result: %a" Grammar.pp_res r);
  (if !is_debug_mode then (
     Format.printf "\n%s\n\n" @@ show_expr e;
     Format.printf "****** Label Table ******\n";
     Interpreter.Interp.print_myexpr myexpr;
     Format.printf "****** Label Table ******\n\n"))
  [@coverage off];

  clean_up ();

  (* if verify then verify_result r; *)
  r

(* DDE kinda similar to mCFA *)
(* performance bottleneck with checking if two sets are same if we were to cache with S set. Zach's library to give unique id for a set *)
(* fancy caching scheme to tell how to catch up (timestamped cache entries) *)

(* make rules more clear *)
(* what's the relationship between judgements holding: e and e1, x twice deep in e1 in Var Non-Local *)
