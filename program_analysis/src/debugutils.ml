[@@@coverage off]

open Utils

let is_debug_mode = ref false

let parse s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string
  |> Interp.Parser.main Interp.Lexer.token

let parse_analyze ?(verify = true) ?(name = "test") s =
  s |> parse |> Lib.analyze ~debug_mode:!is_debug_mode ~verify

let unparse = Format.asprintf "%a" pp_res

let parse_analyze_unparse ?(verify = true) ?(name = "test") s =
  s |> parse_analyze ~verify ~name |> unparse

let pau = parse_analyze_unparse

let parse_analyze_print s =
  s |> parse_analyze |> Format.printf "==> %a\n" pp_res
