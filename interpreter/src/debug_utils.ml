let is_debug_mode = ref false
let should_simplify = ref false
let report_runtime = ref false
let caching = ref true
let eval = Lib.eval

let parse s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token

let parse_eval s =
  s |> parse
  |> Lib.eval ~is_debug_mode:!is_debug_mode ~should_simplify:!should_simplify
       ~caching:!caching
  |> fun (r, runtime) ->
  if !report_runtime then Format.printf "runtime: %f\n" runtime;
  r

let unparse = Format.asprintf "%a" Pp.pp_result_value
let parse_eval_unparse s = s |> parse_eval |> unparse
let peu = parse_eval_unparse

let parse_eval_print s =
  s |> parse_eval |> Format.printf "==> %a\n" Pp.pp_result_value
