open Program_analysis

let pau s =
  Lexing.from_string s
  |> Ddeparser.main Ddelexer.token
  |> Lib.analyze
  |> Format.asprintf "%a" Utils.pp_result_value
