open Core
open Interp.Ast
open Grammar
open Grammar.Atom

let pf = Format.printf
let pfl = pf "%s\n"
let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)
let take_sigma ?(k = 2) = Fn.flip List.take (k - 1)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

let pp_pair fmt (l, s) = Format.fprintf fmt "(%d, %s)" l @@ show_sigma s
let pp_pair_list fmt ls = Format.pp_print_list pp_pair fmt ls
let is_debug_mode = ref false
let ff = Format.fprintf

let rec pp_atom fmt = function
  | IntAnyAtom -> ff fmt "Int"
  | IntAtom i -> ff fmt "%d" i
  | BoolAtom b -> ff fmt "%b" b
  | FunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
  | LStubAtom (l, sigma) ->
      (* ff fmt "stub@(%d,%a)" l pp_sigma sigma *)
      ff fmt "stub"
  | EStubAtom (e, sigma) ->
      (* ff fmt "stub@(%a,%a)" Interp.Pp.pp_expr e pp_sigma sigma *)
      ff fmt "stub"
  | RecAtom entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_record_atom entries
  | ProjAtom (r, Ident s) -> ff fmt "(%a.%s)" pp_res (Set.elements r) s
  | InspAtom (Ident s, r) -> ff fmt "(%s in %a)" s pp_res (Set.elements r)
  | AssertAtom (_, r, _) -> ff fmt "%a" pp_res (Set.elements r)

and pp_record_atom fmt = function
  | [] -> ()
  | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x pp_res (Set.elements v)
  | (Ident x, r) :: rest ->
      Format.fprintf fmt "%s = %a; %a" x pp_res (Set.elements r) pp_record_atom
        rest

and pp_res fmt r =
  if List.is_empty r then ff fmt "#" else ff fmt "%a" pp_res_aux r

and pp_res_aux fmt = function
  | [] -> ()
  | [ a ] -> ff fmt "%a" pp_atom a
  | a :: _as -> ff fmt "%a | %a" pp_atom a pp_res _as
