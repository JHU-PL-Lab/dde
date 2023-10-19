open Core
open Interp

let parse s =
  s |> Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Ast.assign_depth

let unparse e = Format.asprintf "%a" Pp.pp_res e
let parse_eval s = eval (parse s)
let parse_eval_unparse s = s |> parse |> eval |> unparse
let peu = parse_eval_unparse
