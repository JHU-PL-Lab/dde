open Ddeast

exception Unreachable

type label_t = int
type sigma_t = label_t list
type set_t = sigma_t list
type v_t = (sigma_t * expr) list

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
[@@deriving show { with_path = false }]

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let contains_sigma sigma_parent sigma_child =
  List.for_all (fun x -> List.mem x sigma_parent) sigma_child

let stub v e sigma res_pair =
  match List.find_opt (fun (sigma', e') -> sigma = sigma' && e = e') v with
  | Some (_, e) -> (StubResult { e; sigma }, snd res_pair)
  | None -> res_pair

let rec analyze_aux e sigma set v =
  match e with
  | Int i -> stub v e sigma (IntResult i, set)
  | Bool b -> stub v e sigma (BoolResult b, set)
  | Function (Ident x, e', l) ->
      stub v e sigma (FunResult { f = e; l; sigma }, set)
  | Appl (e, e', l) -> (
      match stub ((sigma, e) :: v) e sigma (analyze_aux e sigma set v) with
      | ChoiceResult { res_ls; l = _; sigma = _ }, _ ->
          let result_list, set_union =
            List.fold_right
              (fun fun_res (result_accum, set_accum) ->
                match fun_res with
                | FunResult { f = Function (_, e_i, _); l = _; sigma = _ } -> (
                    match
                      stub v e_i sigma (analyze_aux e_i (l :: sigma) set v)
                    with
                    | res_i, set_i -> (res_i :: result_accum, set_i @ set_accum)
                    )
                | _ -> raise Unreachable [@coverage off])
              res_ls ([], [])
          in
          (ChoiceResult { res_ls = result_list; l; sigma }, set_union)
      | _ -> raise Unreachable [@coverage off])
  | Var (Ident x, l) -> (
      match get_outer_scope l with
      | Function (Ident x1, _, _) -> (
          if x = x1 then
            (* Var Local *)
            match get_expr (List.hd sigma) with
            | Appl (_, e2, l') ->
                (* enumerate all matching stacks in set *)
                let result_list, set_union =
                  List.fold_left
                    (fun ((result_accum, set_accum) as accum) sigma0 ->
                      if List.hd sigma0 = l' && contains_sigma sigma0 sigma then
                        let result_i, set_i =
                          analyze_aux e2 (List.tl sigma0) set v
                        in
                        (result_i :: result_accum, set_i @ set_accum)
                      else accum)
                    ([], []) set
                in
                ( ChoiceResult { res_ls = result_list; l; sigma = List.tl sigma },
                  set_union )
            | _ -> raise Unreachable [@coverage off]
          else
            (* Var Non-Local *)
            match get_expr (List.hd sigma) with
            | Appl (e1, _, l2) -> (
                match analyze_aux e1 sigma set v with
                | FunResult { f; l = l1; sigma = sigma1 }, set1 ->
                    analyze_aux (Var (Ident x, l1)) sigma1 set1 v
                | _ -> raise Unreachable [@coverage off])
            | _ -> raise Unreachable [@coverage off])
      | _ -> raise Unreachable [@coverage off])
  | _ -> raise Unreachable [@coverage off]

let analyze e = analyze_aux e [] [] []
