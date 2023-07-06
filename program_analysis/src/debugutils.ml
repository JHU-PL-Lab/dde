[@@@coverage off]

open Lib
open Utils

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
