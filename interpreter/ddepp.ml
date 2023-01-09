[@@@coverage off]

open Ddeast
open Ddeinterp

let ff = Format.fprintf

let paren_if cond pp fmt e =
  if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

let is_compound_expr = function Var _ -> false | _ -> true

let rec pp_expr fmt (e : expr) =
  match e with
  | Int i -> ff fmt "%d" i
  | Bool b -> ff fmt "%b" b
  | Function (Ident i, x, l) ->
      ff fmt "@[<hv>function %s ->@;<1 4>%a@]" i pp_expr x
  | Var (Ident x, l) -> ff fmt "%s" x
  | Appl (e1, e2, l) ->
      let is_compound_exprL = function
        | Appl _ -> false
        | other -> is_compound_expr other
      in
      ff fmt "%a %a"
        (paren_if is_compound_exprL pp_expr)
        e1
        (paren_if is_compound_expr pp_expr)
        e2
  | Plus (e1, e2, l) -> ff fmt "%a + %a" pp_expr e1 pp_expr e2
  | Minus (e1, e2, l) -> ff fmt "%a + %a" pp_expr e1 pp_expr e2
  | Equal (e1, e2, l) -> ff fmt "%a = %a" pp_expr e1 pp_expr e2
  | And (e1, e2, l) -> ff fmt "%a and %a" pp_expr e1 pp_expr e2
  | Or (e1, e2, l) -> ff fmt "%a or %a" pp_expr e1 pp_expr e2
  | Not (e1, l) -> ff fmt "not %a" pp_expr e1
  | If (e1, e2, e3, l) ->
      ff fmt "@[<hv>if %a then@;<1 4>%a@;<1 0>else@;<1 4>%a@]" pp_expr e1
        pp_expr e2 pp_expr e3
  | Let (Ident i, e1, e2, l) ->
      ff fmt "@[<hv>let %s =@;<1 4>%a@;<1 0>In@;<1 4>%a@]" i pp_expr e1 pp_expr
        e2

let rec pp_result_value fmt (v : result_value) =
  match v with
  | IntResult x -> ff fmt "%d" x
  | BoolResult b -> ff fmt "%b" b
  | FunResult { f; l; sigma } -> (
      match f with
      | Function (Ident i, le, l) ->
          ff fmt "@[<hv>function %s ->@;<1 4>%a@]" i pp_expr le
      | _ -> raise Unreachable)
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2) ->
          ff fmt "%a + %a" pp_result_value r1 pp_result_value r2
      | MinusOp (r1, r2) ->
          ff fmt "%a - %a" pp_result_value r1 pp_result_value r2
      | EqualOp (r1, r2) ->
          ff fmt "%a = %a" pp_result_value r1 pp_result_value r2
      | AndOp (r1, r2) ->
          ff fmt "%a and %a" pp_result_value r1 pp_result_value r2
      | OrOp (r1, r2) -> ff fmt "%a or %a" pp_result_value r1 pp_result_value r2
      | NotOp r1 -> ff fmt "not %a" pp_result_value r1)

let rec pp_fbtype fmt = function
  | TArrow (t1, t2) ->
      let is_arrow = function TArrow (_, _) -> true | _ -> false in
      ff fmt "%a -> %a" (paren_if is_arrow pp_fbtype) t1 pp_fbtype t2
  | TVar s -> ff fmt "%s" s

let show_expr (le : expr) = Format.asprintf "%a" pp_expr le
let show_fbtype t = Format.asprintf "%a" pp_fbtype t
