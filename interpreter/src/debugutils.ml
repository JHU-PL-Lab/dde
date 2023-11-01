[@@@coverage off]

let is_debug_mode = ref false
let should_simplify = ref false
let eval = Lib.eval

let parse s =
  let lexbuf = Lexing.from_string (s ^ ";;") in
  Parser.main Lexer.token lexbuf

let unparse v = Format.asprintf "%a" Pp.pp_result_value v

let parse_eval s =
  Lib.eval (parse s) ~is_debug_mode:!is_debug_mode
    ~should_simplify:!should_simplify

let parse_eval_unparse s =
  unparse
  @@ Lib.eval (parse s) ~is_debug_mode:!is_debug_mode
       ~should_simplify:!should_simplify

let peu = parse_eval_unparse

let parse_eval_print s =
  Format.printf "==> %a\n" Pp.pp_result_value
    (Lib.eval (parse s) ~is_debug_mode:!is_debug_mode
       ~should_simplify:!should_simplify)

(* let pp s = s |> parse |> unparse |> print_string |> print_newline *)
