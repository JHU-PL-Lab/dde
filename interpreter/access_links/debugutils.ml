open Interp

let parse s =
  let lexbuf = Lexing.from_string (s ^ ";;") in
  Parser.main Lexer.token lexbuf

let unparse e = Format.asprintf "%a" Pp.pp_res e
let parse_eval s = eval (parse s)
let parse_eval_unparse s = s |> parse |> eval |> unparse
let peu = parse_eval_unparse
