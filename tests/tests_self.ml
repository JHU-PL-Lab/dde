open OUnit2
open Utils

let test_laziness _ =
  assert_equal
    (dde_eval "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3));;")
    (dde_parse "fun y -> (fun z -> z + 1) (1 + 2 + 3)");
  assert_equal
    (dde_eval "(fun x -> fun y -> x) (if true then 1 else 0);;")
    (dde_parse "fun y -> if true then 1 else 0")

let test_memoization _ =
  assert_equal (dde_eval (Tests_subst.dde_fib 100)) (dde_parse "5050")

let dde_self_tests =
  [ "Laziness" >:: test_laziness; "Memoization" >:: test_memoization ]

let dde_self = "DDE against self" >::: dde_self_tests
