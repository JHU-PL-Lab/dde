[@@@coverage off]

open Ddeast

let ff = Format.fprintf

let paren_if cond pp fmt e =
  if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

let is_compound_expr = function Var _ -> false | _ -> true

let rec pp_expr fmt = function
  | Int (x, label) -> ff fmt "(%d)^%d" x label
  | Var (Ident x, label) -> ff fmt "(%s)^%d" x label
  | Bool (b, label) -> ff fmt "(%b)^%d" b label
  | Function (Ident i, x, label) ->
      ff fmt "(@[<hv>function %s ->@;<1 4>%a@])^%d" i pp_expr x label
  | Appl (e1, e2, label) ->
      let is_compound_exprL = function
        | Appl _ -> false
        | other -> is_compound_expr other
      in
      ff fmt "(%a %a)^%d"
        (paren_if is_compound_exprL pp_expr)
        e1
        (paren_if is_compound_expr pp_expr)
        e2 label
  | Plus (e1, e2, label) -> ff fmt "(%a + %a)^%d" pp_expr e1 pp_expr e2 label
  | Minus (e1, e2, label) -> ff fmt "(%a + %a)^%d" pp_expr e1 pp_expr e2 label
  | Equal (e1, e2, label) -> ff fmt "(%a = %a)^%d" pp_expr e1 pp_expr e2 label
  | And (e1, e2, label) -> ff fmt "(%a and %a)^%d" pp_expr e1 pp_expr e2 label
  | Or (e1, e2, label) -> ff fmt "(%a and %a)^%d" pp_expr e1 pp_expr e2 label
  | Not (e1, label) -> ff fmt "(not %a)^%d" pp_expr e1 label
  | If (e1, e2, e3, label) ->
      ff fmt "(@[<hv>if %a then@;<1 4>%a@;<1 0>else@;<1 4>%a@])^%d" pp_expr e1
        pp_expr e2 pp_expr e3 label
  | Let (Ident i, e1, e2, label) ->
      ff fmt "(@[<hv>let %s =@;<1 4>%a@;<1 0>In@;<1 4>%a@])^%d" i pp_expr e1
        pp_expr e2 label

let rec pp_fbtype fmt = function
  | TArrow (t1, t2) ->
      let is_arrow = function TArrow (_, _) -> true | _ -> false in
      ff fmt "%a -> %a" (paren_if is_arrow pp_fbtype) t1 pp_fbtype t2
  | TVar s -> ff fmt "%s" s

let show_expr e = Format.asprintf "%a" pp_expr e
let show_fbtype t = Format.asprintf "%a" pp_fbtype t
