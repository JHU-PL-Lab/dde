open Ddeast

exception Unreachable

type label_t = int
type sigma_t = label_t list
type set_t = sigma_t list
type vis_t = (sigma_t * expr) list

type op_result_value =
  | PlusOp of result_value * result_value
  | MinusOp of result_value * result_value
  | EqualOp of result_value * result_value
  | AndOp of result_value * result_value
  | OrOp of result_value * result_value
  | NotOp of result_value

and result_value =
  | OpResult of op_result_value
  | ChoiceResult of { res_ls : result_value list; l : label_t; sigma : sigma_t }
  | FunResult of { f : expr; l : label_t; sigma : sigma_t }
  (*? shouldn't we need expr in addition to l to uniquely identify? *)
  | StubResult of { e : expr; sigma : sigma_t }
  | IntResult of int
  | BoolResult of bool

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let rec contains_sigma sigma_parent sigma_child =
  match (sigma_child, sigma_parent) with
  | [], [] -> true (* realistically won't happen *)
  | l_child :: ls_child, l_parent :: ls_parent ->
      l_child = l_parent && contains_sigma ls_parent ls_child
  | [], _ -> true
  | _, [] -> false

(* pass in result-set pair to be returned if not visited *)
let stub_base v e sigma res_pair =
  match List.find_opt (fun (sigma', e') -> sigma = sigma' && e = e') v with
  | Some _ -> (StubResult { e; sigma }, snd res_pair)
  | None -> res_pair

let rec stub_step e sigma set v =
  match List.find_opt (fun (sigma', e') -> sigma = sigma' && e = e') v with
  | Some _ -> (StubResult { e; sigma }, set)
  | None -> analyze_aux e sigma set v

and analyze_aux e sigma set vis =
  match e with
  | Int i -> stub_base vis e sigma (IntResult i, set)
  | Bool b -> stub_base vis e sigma (BoolResult b, set)
  | Function (_, _, l) ->
      (*? should ChoiceResult wrap all results? *)
      stub_base vis e sigma
        ( ChoiceResult { res_ls = [ FunResult { f = e; l; sigma } ]; l; sigma },
          set )
  | Appl (e', _, l) -> (
      let v' = (sigma, e) :: vis in
      match stub_step e' sigma set v' with
      | ChoiceResult { res_ls; l = _; sigma = _ }, _ ->
          let result_list, set_union =
            (* fold_right to keep output choices in the same order *)
            List.fold_right
              (fun fun_res (result_accum, set_accum) ->
                match fun_res with
                | FunResult { f = Function (_, e_i, _); l = _; sigma = _ } ->
                    let sigma' = l :: sigma in
                    let res_i, set_i =
                      (*? set element insertion notation is a bit off *)
                      stub_step e_i (prune_sigma sigma') (sigma' :: set) v'
                    in
                    (*? don't union? *)
                    (res_i :: result_accum, set_i)
                | _ -> raise Unreachable [@coverage off])
              res_ls ([], [])
          in
          (ChoiceResult { res_ls = result_list; l; sigma }, set_union)
      | _ -> raise Unreachable [@coverage off])
  | Var (Ident x, l) -> (
      let sigma_hd = List.hd sigma in
      let sigma_tl = List.tl sigma in
      match get_outer_scope l with
      | Function (Ident x1, _, _) -> (
          if x = x1 then
            (* Var Local *)
            match get_expr sigma_hd with
            | Appl (_, e2, l') ->
                (* enumerate all matching stacks in the set *)
                let result_list, set_union =
                  List.fold_right
                    (fun sigma_i ((result_accum, set_accum) as accum) ->
                      if
                        List.hd sigma_i = l'
                        && contains_sigma (List.tl sigma_i) sigma_tl
                      then
                        let res_i, set_i =
                          (*? pass original sigma (unpopped) to stub? *)
                          stub_step e2 (List.tl sigma_i) set ((sigma, e) :: vis)
                        in
                        (res_i :: result_accum, set_i @ set_accum)
                      else accum)
                    set ([], [])
                in
                ( ChoiceResult { res_ls = result_list; l; sigma = sigma_tl },
                  set_union )
            | _ -> raise Unreachable [@coverage off]
          else
            (* Var Non-Local *)
            match get_expr sigma_hd with
            | Appl (e1, _, l2) -> (
                match analyze_aux e1 sigma set vis with
                | FunResult { f; l = l1; sigma = sigma1 }, set1 ->
                    analyze_aux (Var (Ident x, l1)) sigma1 set1 vis
                | _ -> raise Unreachable [@coverage off])
            | _ -> raise Unreachable [@coverage off])
      | _ -> raise Unreachable [@coverage off])
  | _ -> raise Unreachable [@coverage off]

let analyze e =
  let e = transform_let e in
  fill_my_fun e None;
  analyze_aux e [] [] []

(* TODO: multiple layers of ChoiceResult - improve output readability *)
