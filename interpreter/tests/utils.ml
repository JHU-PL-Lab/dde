open Core
open Interp

exception Unreachable

let assert_equal = OUnit2.assert_equal ~printer:Fn.id

let assert_unequal e1 e2 =
  OUnit2.assert_equal ~cmp:(fun a b -> String.(a <> b)) ~printer:Fn.id e1 e2

let peu ?(should_simplify = false) s =
  s |> Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Lib.eval ~is_debug_mode:false ~should_simplify
  |> Format.asprintf "%a" Pp.pp_result_value
