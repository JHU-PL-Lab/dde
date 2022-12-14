[@@@coverage off]

let analyze = Lib.analyze
let parse s = s ^ ";;" |> Lexing.from_string |> Ddeparser.main Ddelexer.token
let unparse v = v |> Format.asprintf "%a" Utils.pp_result_value
let parse_analyze s = s |> parse |> analyze
let parse_analyze_unparse s = s |> parse |> analyze |> fst |> unparse
let pau = parse_analyze_unparse

let parse_eval_print s =
  s |> parse |> analyze |> fst |> Format.printf "==> %a\n" Utils.pp_result_value
