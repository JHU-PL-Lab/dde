open Ast
open Interp

let ff = Format.fprintf

let paren_if cond pp fmt e =
  if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

let is_compound_expr = function ALVar _ -> false | _ -> true

let rec pp_expr fmt = function
  | ALInt i -> ff fmt "%d" i
  | ALBool b -> ff fmt "%b" b
  | ALVar (Ident x, d) -> ff fmt "%s@%d" x d
  | ALFun (Ident i, x) -> ff fmt "@[<hv>fun %s ->@;<1 4>%a@]" i pp_expr x
  | ALApp (e1, e2) ->
      let is_compound_exprL = function
        | ALApp _ -> false
        | other -> is_compound_expr other
      in
      ff fmt "%a %a"
        (paren_if is_compound_exprL pp_expr)
        e1
        (paren_if is_compound_expr pp_expr)
        e2
  | _ -> failwith "ayo"

let rec pp_res fmt = function
  | ALIntRes i -> ff fmt "%d" i
  | ALBoolRes b -> ff fmt "%b" b
  | ALFunRes (e, _) -> ff fmt "%a" pp_expr e
  | ALPlusRes (r1, r2) -> ff fmt "%a + %a" pp_res r1 pp_res r2
  | ALMinusRes (r1, r2) -> ff fmt "%a - %a" pp_res r1 pp_res r2
  | ALMultRes (r1, r2) -> ff fmt "%a * %a" pp_res r1 pp_res r2
  | ALEqRes (r1, r2) -> ff fmt "%a = %a" pp_res r1 pp_res r2
  | ALGeRes (r1, r2) -> ff fmt "%a >= %a" pp_res r1 pp_res r2
  | ALGtRes (r1, r2) -> ff fmt "%a > %a" pp_res r1 pp_res r2
  | ALLeRes (r1, r2) -> ff fmt "%a <= %a" pp_res r1 pp_res r2
  | ALLtRes (r1, r2) -> ff fmt "%a < %a" pp_res r1 pp_res r2
  | ALAndRes (r1, r2) -> ff fmt "%a && %a" pp_res r1 pp_res r2
  | ALOrRes (r1, r2) -> ff fmt "%a || %a" pp_res r1 pp_res r2
  | ALNotRes r -> ff fmt "not %a" pp_res r
