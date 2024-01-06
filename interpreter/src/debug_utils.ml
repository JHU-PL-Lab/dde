(** Utilies used in utop *)

let debug = ref false
let simplify = ref false
let report_runtime = ref false
let caching = ref true
let eval = Lib.eval

let parse s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token

let parse_eval s =
  s |> parse |> Lib.eval ~debug:!debug ~simplify:!simplify ~caching:!caching
  |> fun (r, runtime) ->
  if !report_runtime then Format.printf "runtime: %fs\n" runtime;
  r

let unparse = Format.asprintf "%a" Pp.pp_result_value
let parse_eval_unparse s = s |> parse_eval |> unparse

(* Main function to execute the interpreter on a program string *)
let peu = parse_eval_unparse

let parse_eval_print s =
  s |> parse_eval |> Format.printf "==> %a\n" Pp.pp_result_value
