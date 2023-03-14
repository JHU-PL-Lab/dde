[@@@coverage off]

open Interpreter

let analyze = Lib.analyze
let parse s = s ^ ";;" |> Lexing.from_string |> Parser.main Lexer.token
let unparse v = v |> Format.asprintf "%a" Utils.pp_result_value
let parse_analyze s = s |> parse |> analyze
let parse_analyze_unparse s = s |> parse |> analyze |> unparse
let pau = parse_analyze_unparse

let parse_eval_print s =
  s |> parse |> analyze |> Format.printf "==> %a\n" Utils.pp_result_value
