open Core
open Logs
open Dinterp
open Dinterp.Ast
open Dinterp.Interp
open Grammar
open Grammar.DAtom
open Utils
open Pa.Exns
open Pa.Logging

let rec prune_d ?(k = 1) d =
  map_d d ~f:(fun (l, d) -> (l, if k = 0 then DNil else prune_d d ~k:(k - 1)))

let rec matches_d d d' =
  compare_d d d' = 0
  || compare_d d DNil = 0
  || length_d d = length_d d'
     && for_all2_d d d' ~f:(fun (l, d) (l', d') -> l = l' && matches_d d d')

let eq_label (l, d, s) (l', d', s') =
  l = l' && compare_d d d' = 0 && Set.compare_direct s s' = 0

let rec vfrag = function
  | DNil -> DNil
  | DCons ((e, d'), _) -> (e, vfrag d') => DNil

let vfrag_s = Set.map (module DS_key) ~f:vfrag

let rec exists_stub r label =
  Set.exists r ~f:(function
    | DFunAtom _ | DIntAnyAtom | DIntAtom _ | DBoolAtom _ -> false
    | DStubAtom label' -> eq_label label label'
    | DProjAtom (r, _) | DInspAtom (_, r) -> exists_stub r label
    | DRecAtom entries ->
        List.exists entries ~f:(fun (_, r) -> exists_stub r label))

let elim_stub r label =
  if not (exists_stub r label) then r
  else
    let bases =
      Set.filter_map
        (module DRes_key)
        r
        ~f:(fun a ->
          match a with
          | DRecAtom _ when not (exists_stub (dres_singleton a) label) -> Some a
          | DFunAtom _ -> Some a
          | _ -> None)
    in
    let fin =
      Set.fold r ~init:dres_empty ~f:(fun acc a ->
          match a with
          | DProjAtom (r_proj, id) -> (
              match Set.elements r_proj with
              | [ DStubAtom label' ] when eq_label label label' ->
                  Set.fold bases ~init:acc ~f:(fun acc -> function
                    | DRecAtom rs -> (
                        match
                          List.find rs ~f:(fun (id', _) ->
                              compare_ident id id' = 0)
                        with
                        | Some (_, r) -> Set.union acc r
                        | None ->
                            (* TODO: this is fine? *)
                            acc)
                    | a' ->
                        Format.printf "r: %a\n" pp_dres r;
                        Format.printf "a: %a\n" pp_datom a;
                        Format.printf "base: %a\n" pp_datom a';
                        raise Runtime_error)
              | _ ->
                  (* TODO: can be a stub of a different label *)
                  Set.add acc a)
          | DStubAtom label' when eq_label label label' -> acc
          | a -> Set.add acc a)
    in
    (* Format.printf "after: %a\n" pp_dres fin; *)
    fin

let minisleep () =
  ignore
    ((Core_unix.select ~read:[] ~write:[] ~except:[]
        ~timeout:(`After Time_ns.Span.second))
       ())

let rec analyze expr d s sfrag v level =
  (* Logs.debug (fun m -> m "Level: %d" level); *)
  let r, s, sfrag =
    let level = level + 1 in
    match expr with
    | DInt i -> (dres_singleton (DIntAtom i), s, sfrag)
    | DBool b -> (dres_singleton (DBoolAtom b), s, sfrag)
    | DFun (id, e) -> (dres_singleton (DFunAtom (expr, d)), s, sfrag)
    | DApp (e, e', l) ->
        debug (fun m -> m "====== DApp (%a) ======" Pp.pp_expr expr);
        let stub_key = (l, d, sfrag) in
        if Set.mem v stub_key then (
          debug (fun m -> m "Stubbed DApp");
          (dres_singleton (DStubAtom stub_key), s, sfrag))
        else (
          debug_plain "Didn't stub DApp";
          debug (fun m -> m "Key (expr): %d" (get_label expr));
          debug (fun m -> m "Key (D): %a" Pp.pp_d d);
          debug (fun m -> m "Key (S): %a" pp_s s);
          debug (fun m -> m "V:\n%a" pp_v v);
          let r1, s1, sfrag1 = analyze e d s sfrag (Set.add v stub_key) level in
          let s_new =
            Set.filter_map
              (module DS_key)
              r1
              ~f:(function
                | DFunAtom (_, d1) -> Some ((l, d) => d1 |> prune_d) | _ -> None)
          in
          let sfrag_new = vfrag_s s_new in
          let v_new =
            Set.singleton (module DV_key) (l, d, Set.union sfrag1 sfrag_new)
          in
          let s = Set.union s1 s_new in
          let sfrag = Set.union sfrag1 sfrag_new in
          let v = Set.union v v_new in
          let fin =
            Set.fold r1 ~init:(dres_empty, s_empty, s_empty)
              ~f:(fun ((acc_r, acc_s, acc_sfrag) as acc) -> function
              | DFunAtom (DFun (_, e1), d1) ->
                  let d_new = (l, d) => d1 |> prune_d in
                  let r0, s0, sfrag0 = analyze e1 d_new s sfrag v level in
                  ( Set.union acc_r r0,
                    Set.union acc_s s0,
                    Set.union acc_sfrag sfrag0 )
              | _ -> acc)
            |> fun (r, s, sfrag) -> (elim_stub r stub_key, s, sfrag)
          in
          debug (fun m -> m "****** DApp (%a) ******" Pp.pp_expr expr);
          fin)
    | DVar (_, m, l) ->
        debug (fun m ->
            m "[Level %d] ====== DVar (%a) ======" level Pp.pp_expr expr);
        let stub_key = (l, d, sfrag) in
        if Set.mem v stub_key then (
          debug (fun m ->
              m "[Level %d] Stubbed DVar (%a)" level Pp.pp_expr expr);
          (dres_singleton (DStubAtom stub_key), s, sfrag))
        else (
          debug_plain "Didn't stub DVar";
          debug (fun m -> m "Key (expr): %a" Pp.pp_expr expr);
          debug (fun m -> m "Key (D): %a" Pp.pp_d d);
          debug (fun m -> m "Key (S): %a" pp_s s);
          debug (fun m -> m "V:\n%a" pp_v v);
          let l_app, _ = nth_exn_d d m in
          let fin =
            Set.fold s ~init:(dres_empty, s_empty, s_empty)
              ~f:(fun ((acc_r, acc_s, acc_sfrag) as acc) d1 ->
                let l_app', d2 = hd_exn_d d1 in
                if l_app = l_app' then (
                  debug (fun m ->
                      m "[Level %d][DVar (%a)] Stitched: %a" level Pp.pp_expr
                        expr Pp.pp_d d1);
                  match Hashtbl.find_exn myexpr l_app with
                  | DApp (_, em', _) ->
                      debug (fun m -> m "em': %a" Pp.pp_expr em');
                      let r0, s0, sfrag0 =
                        analyze em' d2 s sfrag (Set.add v stub_key) level
                      in
                      ( Set.union acc_r r0,
                        Set.union acc_s s0,
                        Set.union acc_sfrag sfrag0 )
                  | _ -> raise Unreachable)
                else acc)
            (* if not (m < length_d d1) then acc
               else if m - 1 >= 0 then (
                 let l_app, d = nth_exn_d d m in
                 debug_plain "m - 1 case";
                 let l_app', d' = nth_exn_d d1 (m - 1) in
                 if l_app = l_app' then (
                   debug (fun m ->
                       m "[Level %d][DVar (%a)] Stitched!" level Pp.pp_expr
                         expr);
                   debug (fun m_ -> m_ "Accessing index %d of %a" m Pp.pp_d d1);
                   let d2 = d' in
                   match Hashtbl.find_exn myexpr l_app with
                   | DApp (_, em', _) ->
                       debug (fun m -> m "em': %a" Pp.pp_expr em');
                       let r0, s0, sfrag0 =
                         analyze em' d2 s sfrag (Set.add v stub_key) level
                       in
                       ( Set.union acc_r r0,
                         Set.union acc_s s0,
                         Set.union acc_sfrag sfrag0 )
                   | _ -> raise Unreachable)
                 else acc)
               else if matches_d d d1 then (
                 debug_plain "m case";
                 debug (fun m ->
                     m "[Level %d][DVar (%a)] Stitched!" level Pp.pp_expr expr);
                 debug (fun m_ -> m_ "Accessing index %d of %a" m Pp.pp_d d1);
                 let l_app, d2 = nth_exn_d d1 m in
                 debug (fun m -> m "d2: %a" Pp.pp_d d2);
                 match Hashtbl.find_exn myexpr l_app with
                 | DApp (_, em', _) ->
                     debug (fun m -> m "em': %a" Pp.pp_expr em');
                     let r0, s0, sfrag0 =
                       analyze em' d2 s sfrag (Set.add v stub_key) level
                     in
                     ( Set.union acc_r r0,
                       Set.union acc_s s0,
                       Set.union acc_sfrag sfrag0 )
                 | _ -> raise Unreachable)
               else acc) *)
            |>
            fun (r, s, sfrag) -> (elim_stub r stub_key, s, sfrag)
          in
          debug (fun m ->
              m "[Level %d] ****** DVar (%a) ******" level Pp.pp_expr expr);
          fin)
    | DIf (e1, e2, e3) ->
        debug (fun m ->
            m "[Level %d] ====== DIf (%a) ======" level Pp.pp_expr expr);
        let r_cond, s_cond, sfrag_cond = analyze e1 d s sfrag v level in
        let r_cond = Set.elements r_cond in
        let fin =
          match r_cond with
          | [ DBoolAtom b ] ->
              debug (fun m -> m "DIf picks branch %b" b);
              if b then analyze e2 d s_cond sfrag_cond v level
              else analyze e3 d s_cond sfrag_cond v level
          | _ ->
              debug (fun m -> m "DIf picks both branches");
              let r1, s1, sfrag1 = analyze e2 d s_cond sfrag_cond v level in
              let r2, s2, sfrag2 = analyze e3 d s1 sfrag1 v level in
              (Set.union r1 r2, s2, sfrag2)
        in
        debug (fun m ->
            m "[Level %d] ****** DIf (%a) ******" level Pp.pp_expr expr);
        fin
    | DPlus (e1, e2) | DMinus (e1, e2) | DMult (e1, e2) ->
        debug (fun m -> m "====== DOp (%a) ======" Pp.pp_expr expr);
        let r1, s1, sfrag1 = analyze e1 d s sfrag v level in
        let r2, s2, sfrag2 = analyze e2 d s1 sfrag1 v level in
        let r1' = Set.elements r1 in
        let r2' = Set.elements r2 in
        let fin =
          match (r1', r2') with
          | [ DIntAtom i1 ], [ DIntAtom i2 ] ->
              ( dres_singleton
                  (DIntAtom
                     ((match expr with
                      | DPlus _ -> ( + )
                      | DMinus _ -> ( - )
                      | DMult _ -> ( * )
                      | _ -> failwith "unimplemented")
                        i1 i2)),
                s2,
                sfrag2 )
          | _ ->
              (* Format.printf "r1: %a | r2: %a\n" pp_dres r1 pp_dres r2; *)
              (dres_singleton DIntAnyAtom, s2, sfrag2)
        in
        debug (fun m -> m "****** DOp (%a) ******" Pp.pp_expr expr);
        fin
    | DAnd (e1, e2) | DOr (e1, e2) ->
        debug (fun m -> m "====== DOp (%a) ======" Pp.pp_expr expr);
        let r1, s1, sfrag1 = analyze e1 d s sfrag v level in
        let r2, s2, sfrag2 = analyze e2 d s1 sfrag1 v level in
        let r1' = Set.elements r1 in
        let r2' = Set.elements r2 in
        let fin =
          match (r1', r2') with
          | [ DBoolAtom b1 ], [ DBoolAtom b2 ] ->
              ( dres_singleton
                  (DBoolAtom
                     ((match expr with
                      | DAnd _ -> ( && )
                      | DOr _ -> ( || )
                      | _ -> raise Unreachable)
                        b1 b2)),
                s2,
                sfrag2 )
          | _ ->
              ( Set.of_list (module DRes_key) [ DBoolAtom true; DBoolAtom false ],
                s2,
                sfrag2 )
        in
        debug (fun m -> m "****** DOp (%a) ******" Pp.pp_expr expr);
        fin
    | DEq (e1, e2) | DGe (e1, e2) | DGt (e1, e2) | DLe (e1, e2) | DLt (e1, e2)
      ->
        debug (fun m -> m "====== DOp (%a) ======" Pp.pp_expr expr);
        let r1, s1, sfrag1 = analyze e1 d s sfrag v level in
        let r2, s2, sfrag2 = analyze e2 d s1 sfrag1 v level in
        let r1' = Set.elements r1 in
        let r2' = Set.elements r2 in
        let fin =
          match (r1', r2') with
          | [ DIntAtom i1 ], [ DIntAtom i2 ] ->
              ( dres_singleton
                  (DBoolAtom
                     ((match expr with
                      | DEq _ -> ( = )
                      | DGe _ -> ( >= )
                      | DGt _ -> ( > )
                      | DLe _ -> ( <= )
                      | DLt _ -> ( < )
                      | _ -> raise Unreachable)
                        i1 i2)),
                s2,
                sfrag2 )
          | _ ->
              ( Set.of_list (module DRes_key) [ DBoolAtom true; DBoolAtom false ],
                s2,
                sfrag2 )
        in
        debug (fun m -> m "****** DOp (%a) ******" Pp.pp_expr expr);
        fin
    | DNot e ->
        (* analyze e d s v *)
        debug (fun m -> m "====== DOp (%a) ======" Pp.pp_expr expr);
        let r, s, sfrag = analyze e d s sfrag v level in
        let r' = Set.elements r in
        let fin =
          match r' with
          | [ DBoolAtom b ] -> (dres_singleton (DBoolAtom (not b)), s, sfrag)
          | _ ->
              ( Set.of_list (module DRes_key) [ DBoolAtom true; DBoolAtom false ],
                s,
                sfrag )
        in
        debug (fun m -> m "****** DOp (%a) ******" Pp.pp_expr expr);
        fin
    | DRec es ->
        if List.is_empty es then (dres_singleton (DRecAtom []), s, sfrag)
        else
          es
          |> List.map ~f:(fun (id, e) -> (id, analyze e d s sfrag v level))
          |> List.map ~f:(fun (id, (r, s, sfrag)) -> ((id, r), s, sfrag))
          |> List.unzip3
          |> fun (rs, ss, sfrags) ->
          ( dres_singleton (DRecAtom rs),
            Set.union_list (module DS_key) ss,
            Set.union_list (module DS_key) sfrags )
    | DProj (e, id) ->
        debug (fun m ->
            m "[Level %d] ====== DProj (%a) ======" level Pp.pp_expr expr);
        let r, s, sfrag = analyze e d s sfrag v level in
        let r = dres_singleton (DProjAtom (r, id)) in
        let fin = (r, s, sfrag) in
        debug (fun m -> m "[DProj] Before simpl.: %a" pp_dres r);
        debug (fun m ->
            m "[Level %d] ****** DProj (%a) ******" level Pp.pp_expr expr);
        fin
    | DInsp (id, e) ->
        let r, s, sfrag = analyze e d s sfrag v level in
        (dres_singleton (DInspAtom (id, r)), s, sfrag)
    | DLetAssert (_, e, _) -> analyze e d s sfrag v level
  in
  let r = Simplifier.simplify r in
  let fin = (r, s, sfrag) in
  debug (fun m -> m "[Level %d] Result: %a" level pp_dres r);
  fin

let analyze expr =
  debug (fun m -> m "myexpr:\n%a" Pp.pp_myexpr Ast.myexpr);
  let r, _, _ =
    analyze expr DNil s_empty s_empty (Set.empty (module DV_key)) 0
  in
  debug (fun m -> m "result:\n%a" pp_dres r);
  r
