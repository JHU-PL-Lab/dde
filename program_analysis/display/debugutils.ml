open Core

let parse s =
  s |> Fn.flip ( ^ ) ";;" |> Lexing.from_string
  |> Dinterp.Parser.main Dinterp.Lexer.token
  |> Dinterp.Ast.assign_depth

let unparse = Format.asprintf "%a" Utils.pp_dres

let parse_analyze s =
  s |> parse |> Lib.analyze |> fun r ->
  Dinterp.Ast.clean_up ();
  r

let parse_analyze_unparse s = s |> parse_analyze |> unparse
let pau = parse_analyze_unparse
