open Core
open Interpreter.Ast
open Grammar

let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

let rec fold_res r ~init ~f =
  match r with
  | LabelResAtom (r, _) :: rs | ExprResAtom (r, _) :: rs ->
      fold_res (r @ rs) ~init ~f
  | r :: rs -> fold_res rs ~init:(f init r) ~f
  | [] -> init

let s_set = Hashset.create 1000

let print_set () =
  Hashset.fold (fun s acc -> show_sigma s ^ "\n" ^ acc) s_set ""

let pp_pair fmt (l, s) = Format.fprintf fmt "(%d, %s)" l @@ show_sigma s
let pp_pair_list fmt ls = Format.pp_print_list pp_pair fmt ls
let is_debug_mode = ref false

let all_combs l1 l2 =
  Set.fold l1 ~init:[] ~f:(fun acc x ->
      Set.fold l2 ~init:[] ~f:(fun acc y -> (x, y) :: acc))
