[@@@coverage off]

open Ddeast

let ff = Format.fprintf

let paren_if cond pp fmt e =
  if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

let is_compound_expr = function Var _, _ -> false | _, _ -> true

let rec pp_lexpr fmt (le : lexpr) =
  let e, label = le in
  match e with
  | Int x -> ff fmt "(%d)^%d" x label
  | Var (Ident x) -> ff fmt "(%s)^%d" x label
  | Bool b -> ff fmt "(%b)^%d" b label
  | Function (Ident i, x) ->
      ff fmt "(@[<hv>function %s ->@;<1 4>%a@])^%d" i pp_lexpr x label
  | Appl (e1, e2) ->
      let is_compound_exprL = function
        | Appl _, _ -> false
        | other -> is_compound_expr other
      in
      ff fmt "(%a %a)^%d"
        (paren_if is_compound_exprL pp_lexpr)
        e1
        (paren_if is_compound_expr pp_lexpr)
        e2 label
  | Plus (e1, e2) -> ff fmt "(%a + %a)^%d" pp_lexpr e1 pp_lexpr e2 label
  | Minus (e1, e2) -> ff fmt "(%a + %a)^%d" pp_lexpr e1 pp_lexpr e2 label
  | Equal (e1, e2) -> ff fmt "(%a = %a)^%d" pp_lexpr e1 pp_lexpr e2 label
  | And (e1, e2) -> ff fmt "(%a and %a)^%d" pp_lexpr e1 pp_lexpr e2 label
  | Or (e1, e2) -> ff fmt "(%a and %a)^%d" pp_lexpr e1 pp_lexpr e2 label
  | Not e1 -> ff fmt "(not %a)^%d" pp_lexpr e1 label
  | If (e1, e2, e3) ->
      ff fmt "(@[<hv>if %a then@;<1 4>%a@;<1 0>else@;<1 4>%a@])^%d" pp_lexpr e1
        pp_lexpr e2 pp_lexpr e3 label
  | Let (Ident i, e1, e2) ->
      ff fmt "(@[<hv>let %s =@;<1 4>%a@;<1 0>In@;<1 4>%a@])^%d" i pp_lexpr e1
        pp_lexpr e2 label

let rec pp_fbtype fmt = function
  | TArrow (t1, t2) ->
      let is_arrow = function TArrow (_, _) -> true | _ -> false in
      ff fmt "%a -> %a" (paren_if is_arrow pp_fbtype) t1 pp_fbtype t2
  | TVar s -> ff fmt "%s" s

let show_lexpr (le : lexpr) = Format.asprintf "%a" pp_lexpr le
let show_fbtype t = Format.asprintf "%a" pp_fbtype t
