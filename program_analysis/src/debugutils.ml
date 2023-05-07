[@@@coverage off]

open Lib

let ff = Format.fprintf

let rec pp_result_value fmt (v : result_value) =
  match v with
  | IntResult x -> ff fmt "%d" x
  | BoolResult b -> ff fmt "%b" b
  | FunResult { f; _ } -> (
      match f with
      | Function (Ident i, le, _) ->
          ff fmt "@[<hv>function %s ->@;<1 4>%a@]" i Interpreter.Pp.pp_expr le
      | _ -> raise Unreachable)
  | ChoiceResult { choices; _ } ->
      if List.length choices = 1 then
        ff fmt "%a" pp_result_value (List.hd choices)
      else
        ff fmt "(%s)"
          (choices
          |> List.map (fun res -> Format.asprintf "%a" pp_result_value res)
          |> String.concat " | ")
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2) ->
          ff fmt "(%a + %a)" pp_result_value r1 pp_result_value r2
      | MinusOp (r1, r2) ->
          ff fmt "(%a - %a)" pp_result_value r1 pp_result_value r2
      | EqualOp (r1, r2) ->
          ff fmt "(%a = %a)" pp_result_value r1 pp_result_value r2
      | AndOp (r1, r2) ->
          ff fmt "(%a and %a)" pp_result_value r1 pp_result_value r2
      | OrOp (r1, r2) ->
          ff fmt "(%a or %a)" pp_result_value r1 pp_result_value r2
      | NotOp r1 -> ff fmt "(not %a)" pp_result_value r1)
  | StubResult { e; _ } -> ff fmt "stub"

let is_debug_mode = ref false

let parse s =
  s ^ ";;" |> Lexing.from_string
  |> Interpreter.Parser.main Interpreter.Lexer.token

let unparse v = v |> Format.asprintf "%a" pp_result_value
let parse_analyze s = s |> parse |> analyze

let parse_analyze_unparse s =
  s |> parse |> analyze ~debug:!is_debug_mode |> unparse

let pau = parse_analyze_unparse

let parse_eval_print s =
  s |> parse
  |> analyze ~debug:!is_debug_mode
  |> Format.printf "==> %a\n" pp_result_value
