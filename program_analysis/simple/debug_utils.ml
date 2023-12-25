let report_runtime = ref false

let parse s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string
  |> Interp.Parser.main Interp.Lexer.token

let parse_analyze ?(name = "test") s =
  s |> parse |> Lib.analyze |> fun (r, runtime) ->
  if !report_runtime then Format.printf "%s: %f\n" name runtime;
  r

let unparse = Format.asprintf "%a" Utils.Res.pp

let parse_analyze_unparse ?(name = "test") s =
  s |> parse_analyze ~name |> unparse

let pau = parse_analyze_unparse

let parse_analyze_print s =
  s |> parse_analyze |> Format.printf "==> %a\n" Utils.Res.pp
