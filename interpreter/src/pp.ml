(** Pretty-printers for the AST and auxiliary data structures *)

open Ast
open Core

let ff = Format.fprintf

let paren_if cond pp fmt e =
  if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

let is_compound_expr = function Var _ -> false | _ -> true

let is_compound_exprL = function
  | App _ -> false
  | other -> is_compound_expr other

let rec pp_expr fmt = function
  | Int i -> ff fmt "%d" i
  | Bool b -> ff fmt "%b" b
  | Fun (Ident i, x, l) -> ff fmt "@[<hv>fun %s ->@;<1 2>%a@]" i pp_expr x
  | Var (Ident x, _) -> ff fmt "%s" x
  | App (e1, e2, _) ->
      ff fmt "%a %a"
        (paren_if is_compound_exprL pp_expr)
        e1
        (paren_if is_compound_expr pp_expr)
        e2
  | Plus (e1, e2) -> ff fmt "(%a + %a)" pp_expr e1 pp_expr e2
  | Minus (e1, e2) -> ff fmt "(%a - %a)" pp_expr e1 pp_expr e2
  | Mult (e1, e2) -> ff fmt "(%a * %a)" pp_expr e1 pp_expr e2
  | Eq (e1, e2) -> ff fmt "(%a = %a)" pp_expr e1 pp_expr e2
  | And (e1, e2) -> ff fmt "(%a and %a)" pp_expr e1 pp_expr e2
  | Or (e1, e2) -> ff fmt "(%a or %a)" pp_expr e1 pp_expr e2
  | Ge (e1, e2) -> ff fmt "(%a >= %a)" pp_expr e1 pp_expr e2
  | Gt (e1, e2) -> ff fmt "(%a > %a)" pp_expr e1 pp_expr e2
  | Le (e1, e2) -> ff fmt "(%a <= %a)" pp_expr e1 pp_expr e2
  | Lt (e1, e2) -> ff fmt "(%a < %a)" pp_expr e1 pp_expr e2
  | Not e1 -> ff fmt "(not %a)" pp_expr e1
  | If (e1, e2, e3) ->
      ff fmt "@[<hv>if %a then@;<1 2>%a@;<1 0>else@;<1 2>%a@]" pp_expr e1
        pp_expr e2 pp_expr e3
  | Let (Ident i, e1, e2, _) ->
      ff fmt "@[<hv>let %s =@;<1 4>%a@;<1 0>in@;<1 4>%a@]" i pp_expr e1 pp_expr
        e2
  | LetAssert (Ident i, e1, e2) ->
      ff fmt "@[<hv>letassert %s =@;<1 4>%a@;<1 0>in@;<1 4>%a@]" i pp_expr e1
        pp_expr e2
  | Rec entries ->
      ff fmt
        (if List.length entries = 0 then "{%a}" else "{ %a }")
        pp_record entries
  | Proj (e, Ident x) -> ff fmt "(%a.%s)" pp_expr e x
  | Insp (Ident x, e) -> ff fmt "(%s in %a)" x pp_expr e

and pp_record fmt = function
  | [] -> ()
  | [ (Ident x, e) ] -> ff fmt "%s = %a" x pp_expr e
  | (Ident x, e) :: rest -> ff fmt "%s = %a; %a" x pp_expr e pp_record rest

let rec pp_result_value fmt = function
  | IntRes x -> ff fmt "%d" x
  | BoolRes b -> ff fmt "%b" b
  | FunRes { f; l; sigma } -> pp_expr fmt f
  | RecRes es ->
      ff fmt
        (if List.length es = 0 then "{%a}" else "{ %a }")
        pp_record_result es
  | PlusRes (r1, r2) -> ff fmt "%a + %a" pp_result_value r1 pp_result_value r2
  | MinusRes (r1, r2) -> ff fmt "%a - %a" pp_result_value r1 pp_result_value r2
  | MultRes (r1, r2) -> ff fmt "%a * %a" pp_result_value r1 pp_result_value r2
  | EqRes (r1, r2) -> ff fmt "%a = %a" pp_result_value r1 pp_result_value r2
  | AndRes (r1, r2) -> ff fmt "%a and %a" pp_result_value r1 pp_result_value r2
  | OrRes (r1, r2) -> ff fmt "%a or %a" pp_result_value r1 pp_result_value r2
  | GeRes (r1, r2) -> ff fmt "%a >= %a" pp_result_value r1 pp_result_value r2
  | GtRes (r1, r2) -> ff fmt "%a > %a" pp_result_value r1 pp_result_value r2
  | LeRes (r1, r2) -> ff fmt "%a <= %a" pp_result_value r1 pp_result_value r2
  | LtRes (r1, r2) -> ff fmt "%a < %a" pp_result_value r1 pp_result_value r2
  | NotRes r1 -> ff fmt "not %a" pp_result_value r1

and pp_record_result fmt = function
  | [] -> ()
  | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x pp_result_value v
  | (Ident x, v) :: rest ->
      Format.fprintf fmt "%s = %a; %a" x pp_result_value v pp_record_result rest

let rec pp_res_val_fv fmt = function
  | IntResFv i -> ff fmt "%d" i
  | BoolResFv b -> ff fmt "%b" b
  | VarResFv (Ident x) -> ff fmt "%s" x
  | GeResFv (v1, v2) -> ff fmt "%a > %a" pp_res_val_fv v1 pp_res_val_fv v2
  | _ -> ()

let string_of_table tbl which =
  Hashtbl.to_alist tbl
  |> List.sort ~compare:(fun (k1, v1) (k2, v2) -> Int.ascending k1 k2)
  |> List.map ~f:(fun (k, v) -> Format.asprintf "%d -> %a" k pp_expr v)
  |> String.concat ~sep:"\n"
  |> fun content ->
  Format.sprintf "=== %s table ===\n%s\n*** %s table ***\n" which content which
