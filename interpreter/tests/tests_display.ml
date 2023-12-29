open OUnit2
open Dinterp

let peu s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Interp.eval
  |> Format.asprintf "%a" Pp.pp_res

let assert_equal exp act = assert_equal ~printer:Core.Fn.id exp act

let test_recursion _ =
  assert_equal "1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 0"
    (peu
       "let id = fun self -> fun n -> if n = 0 then 0 else 1 + self self (n - \
        1) in id id 10");
  assert_equal
    "4 - 1 - 1 - 1 + 4 - 1 - 1 - 2 + 4 - 1 - 2 + 4 - 2 - 1 + 4 - 2 - 2"
    (peu
       "let fib = fun self -> fun n -> if n <= 1 then n else self self (n - 1) \
        + self self (n - 2) in fib fib 4")

let display_tests = [ (* "Recursion" >:: test_recursion *) ]
let dde_display = "DDE against self" >::: display_tests
