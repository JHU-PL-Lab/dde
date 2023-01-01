[@@@coverage off]

let is_debug_mode = ref false
let eval = Fbdk.Interpreter.eval

let parse s =
  let lexbuf = Lexing.from_string (s ^ ";;") in
  Fbdk.Parser.main Fbdk.Lexer.token lexbuf

let unparse v = Format.asprintf "%a" Fbdk.Pp.pp_result_value v
let parse_eval s = Fbdk.Interpreter.eval !is_debug_mode (parse s)

let parse_eval_unparse s =
  unparse @@ Fbdk.Interpreter.eval !is_debug_mode (parse s)

let peu = parse_eval_unparse

let parse_eval_print s =
  Format.printf "==> %a\n" Fbdk.Pp.pp_result_value
    (Fbdk.Interpreter.eval !is_debug_mode (parse s))

(* let pp s = s |> parse |> unparse |> print_string |> print_newline *)
