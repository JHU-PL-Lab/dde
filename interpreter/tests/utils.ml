open Core
open Interp

exception Unreachable

let assert_equal = OUnit2.assert_equal ~printer:Fn.id

let assert_unequal e1 e2 =
  OUnit2.assert_equal ~cmp:(fun a b -> String.(a <> b)) ~printer:Fn.id e1 e2

let report_runtime = ref false
let caching = ref true
let debug = ref false

let peu ?(simplify = false) s =
  s |> Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Lib.eval ~debug:!debug ~simplify ~caching:!caching
  |> fun (r, runtime) ->
  if !report_runtime then Format.printf "runtime: %f\n" runtime;
  r |> Format.asprintf "%a" Pp.pp_result_value
