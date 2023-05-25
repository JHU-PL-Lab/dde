[@@@coverage off]

open Lib
open Grammar

let ff = Format.fprintf

let rec pp_atom fmt (v : atom) =
  match v with
  | IntAtom x -> ff fmt "%d" x
  | BoolAtom b -> ff fmt "%b" b
  | FunAtom (f, _, _) -> (
      match f with
      | Function (Ident i, le, _) ->
          ff fmt "@[<hv>function %s ->@;<1 4>%a@]" i Interpreter.Pp.pp_expr le
      | _ -> raise Unreachable)
  | ResAtom choices | LabelResAtom (choices, _) | ExprResAtom (choices, _) ->
      if List.length choices = 1 then ff fmt "%a" pp_atom (List.hd choices)
      else
        ff fmt "(%s)"
          (choices
          |> List.map (fun res -> Format.asprintf "%a" pp_atom res)
          |> String.concat " | ")
  | OpAtom op -> (
      match op with
      | PlusOp (r1, r2) -> ff fmt "(%a + %a)" pp_res r1 pp_res r2
      | MinusOp (r1, r2) -> ff fmt "(%a - %a)" pp_res r1 pp_res r2
      | EqualOp (r1, r2) -> ff fmt "(%a = %a)" pp_res r1 pp_res r2
      | AndOp (r1, r2) -> ff fmt "(%a and %a)" pp_res r1 pp_res r2
      | OrOp (r1, r2) -> ff fmt "(%a or %a)" pp_res r1 pp_res r2
      | NotOp r1 -> ff fmt "(not %a)" pp_res r1)
  | LabelStubAtom _ | ExprStubAtom _ -> ff fmt "stub"

(* write a list pretty printer using %a *)
and pp_res fmt = function
  | [] -> ()
  | [ a ] -> ff fmt "%a" pp_atom a
  | a :: _as -> ff fmt "(%a | %a)" pp_atom a pp_res _as

let is_debug_mode = ref false

let parse s =
  s ^ ";;" |> Lexing.from_string
  |> Interpreter.Parser.main Interpreter.Lexer.token
  |> fun expr ->
  (* keep labeling consistent across multiple calls
     to `analyze` *)
  Interpreter.Ast.reset_label ();
  expr

let unparse v = Format.asprintf "%a" pp_res v
let parse_analyze s = s |> parse |> analyze ~debug:!is_debug_mode

let parse_analyze_unparse s =
  s |> parse |> analyze ~debug:!is_debug_mode |> unparse

let pau = parse_analyze_unparse

let parse_eval_print s =
  s |> parse |> analyze ~debug:!is_debug_mode |> Format.printf "==> %a\n" pp_res
