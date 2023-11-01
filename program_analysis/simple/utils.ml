open Core
open Interp.Ast
open Grammar

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

let show_set = Set.fold ~init:"" ~f:(fun acc s -> show_sigma s ^ "\n" ^ acc)
let pp_pair fmt (l, s) = Format.fprintf fmt "(%d, %s)" l @@ show_sigma s
let pp_pair_list fmt ls = Format.pp_print_list pp_pair fmt ls
let is_debug_mode = ref false

let all_combs l1 l2 =
  Set.fold l1 ~init:[] ~f:(fun acc x ->
      Set.fold l2 ~init:[] ~f:(fun acc y -> (x, y) :: acc))

let ff = Format.fprintf

let rec pp_atom fmt = function
  | IntAnyAtom -> ff fmt "Int"
  | IntAtom i -> ff fmt "%d" i
  | BoolAtom b -> ff fmt "%b" b
  | FunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
  (* | LabelResAtom (choices, _) -> ff fmt "%a" pp_res choices
     | ExprResAtom (choices, _) -> ff fmt "%a" pp_res choices
     | LabelStubAtom _ -> ff fmt "stub"
     | ExprStubAtom _ -> ff fmt "stub" *)
  (* | LabelResAtom (choices, (l, _)) -> ff fmt "(%a)^%d" pp_res choices l
     | ExprResAtom (choices, (e, _)) ->
         ff fmt "(%a)^%a" pp_res choices Interpreter.Pp.pp_expr e
     | LabelStubAtom (l, _) -> ff fmt "stub@%d" l
     | ExprStubAtom (e, _) -> ff fmt "(stub@%a)" Interpreter.Pp.pp_expr e *)
  (* | OpAtom op -> (
      match op with
      | PlusOp (r1, r2) -> ff fmt "(%a + %a)" pp_res r1 pp_res r2
      | MinusOp (r1, r2) -> ff fmt "(%a - %a)" pp_res r1 pp_res r2
      | MultOp (r1, r2) -> ff fmt "(%a * %a)" pp_res r1 pp_res r2
      | EqualOp (r1, r2) -> ff fmt "(%a = %a)" pp_res r1 pp_res r2
      | AndOp (r1, r2) -> ff fmt "(%a and %a)" pp_res r1 pp_res r2
      | OrOp (r1, r2) -> ff fmt "(%a or %a)" pp_res r1 pp_res r2
      | GeOp (r1, r2) -> ff fmt "(%a >= %a)" pp_res r1 pp_res r2
      | GtOp (r1, r2) -> ff fmt "(%a > %a)" pp_res r1 pp_res r2
      | LeOp (r1, r2) -> ff fmt "(%a <= %a)" pp_res r1 pp_res r2
      | LtOp (r1, r2) -> ff fmt "(%a < %a)" pp_res r1 pp_res r2
      | NotOp r1 -> ff fmt "(not %a)" pp_res r1) *)
  (* | EquivStubAtom (s, l) ->
      ff fmt "{%s}[%d]"
        (s |> Set.to_list
        |> List.map ~f:(fun st -> Format.sprintf "%s" (St.show st))
        |> String.concat ~sep:", ")
        l *)
  (* | PathCondAtom (_, r) -> ff fmt "%a" pp_res r *)
  (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" pp_res r b pp_res r' *)
  | LStubAtom _ -> ff fmt "stub"
  | EStubAtom _ -> ff fmt "stub"
  | RecAtom entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_record_atom entries
  | ProjAtom (r, Ident s) -> ff fmt "(%a.%s)" pp_res r s
  | InspAtom (Ident s, r) -> ff fmt "(%s in %a)" s pp_res r
  | AssertAtom (_, r, _) -> ff fmt "%a" pp_res r

and pp_record_atom fmt = function
  | [] -> ()
  | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x pp_res v
  | (Ident x, v) :: rest ->
      Format.fprintf fmt "%s = %a; %a" x pp_res v pp_record_atom rest

and pp_res fmt = function
  | [] -> ()
  | [ a ] -> ff fmt "%a" pp_atom a
  | a :: _as -> ff fmt "(%a | %a)" pp_atom a pp_res _as
