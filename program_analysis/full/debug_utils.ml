[@@@coverage off]

open Grammar

let parse s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string
  |> Interp.Parser.main Interp.Lexer.token

let parse_analyze ?(verify = true) ?(name = "test") s =
  s |> parse |> Lib.analyze ~verify

let unparse = Format.asprintf "%a" Res.pp

let parse_analyze_unparse ?(verify = true) ?(name = "test") s =
  s |> parse_analyze ~verify ~name |> unparse

let pau = parse_analyze_unparse

let parse_analyze_print s =
  s |> parse_analyze |> Format.printf "==> %a\n" Res.pp
