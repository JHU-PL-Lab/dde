open Program_analysis

let au e = e |> Lib.analyze |> Format.asprintf "%a" Utils.pp_result_value
let pau s = Lexing.from_string s |> Ddeparser.main Ddelexer.token |> au
