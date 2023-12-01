open Lib
open Utils

let is_debug_mode = ref false

let parse s =
  s ^ ";;" |> Lexing.from_string |> Interp.Parser.main Interp.Lexer.token
  |> fun e ->
  (* keep labeling consistent across multiple calls
     to `analyze` *)
  Interp.Ast.reset_label ();
  e

let unparse r = Format.asprintf "%a" pp_res (Core.Set.elements r)
let parse_analyze s = s |> parse |> analyze ~debug_mode:!is_debug_mode
let parse_analyze_unparse s = s |> parse_analyze |> unparse
let pau = parse_analyze_unparse

let parse_analyze_print s =
  s |> parse_analyze |> Core.Set.elements |> Format.printf "==> %a\n" pp_res
