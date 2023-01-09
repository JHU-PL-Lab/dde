open Ddeast

exception Unreachable

type sigma_t = int list
type set_t = sigma_t list

type op_result_value =
  | PlusOp of result_value * result_value
  | MinusOp of result_value * result_value
  | EqualOp of result_value * result_value
  | AndOp of result_value * result_value
  | OrOp of result_value * result_value
  | NotOp of result_value

and result_value =
  | FunResult of { f : expr; l : int; sigma : sigma_t }
  | ChoiceResult of { ls : result_value list; l : int; sigma : sigma_t }
  | IntResult of int
  | BoolResult of bool
  | OpResult of op_result_value
[@@deriving show { with_path = false }]

let prune_sigma ?(k = 2) sigma = List.filteri (fun i _ -> i < k) sigma

let contains_sigma sigma_parent sigma_child =
  List.for_all (fun x -> List.mem x sigma_parent) sigma_child

let rec analyze_aux e sigma set =
  match e with
  | Int i -> (IntResult i, set)
  | Bool b -> (BoolResult b, set)
  | Function (Ident x, e', l) -> (FunResult { f = e; l; sigma }, set)
  | Appl (e1, e2, l) -> (
      match analyze_aux e1 sigma set with
      | FunResult { f = Function (_, e, _); l = _; sigma = _ }, set1 ->
          let sigma' = l :: sigma in
          analyze_aux e (prune_sigma sigma') (sigma' :: set1)
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
                          analyze_aux e2 (List.tl sigma0) set
                        in
                        (result_i :: result_accum, set_i @ set_accum)
                      else accum)
                    ([], []) set
                in
                ( ChoiceResult { ls = result_list; l; sigma = List.tl sigma },
                  set_union )
            | _ -> raise Unreachable [@coverage off]
          else
            (* Var Non-Local *)
            match get_expr (List.hd sigma) with
            | Appl (e1, _, l2) -> (
                match analyze_aux e1 sigma set with
                | FunResult { f; l = l1; sigma = sigma1 }, set1 ->
                    analyze_aux (Var (Ident x, l1)) sigma1 set1
                | _ -> raise Unreachable [@coverage off])
            | _ -> raise Unreachable [@coverage off])
      | _ -> raise Unreachable [@coverage off])
  | _ -> raise Unreachable [@coverage off]

let analyze (e : expr) : result_value * set_t = analyze_aux e [] []
