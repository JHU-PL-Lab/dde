open OUnit2
open Test_utils

let test_basics _ =
  assert_equal "| | 1" (pau "(fun x -> x) 1;;");
  assert_equal "| (1 + | 2)" (pau "(fun y -> 1 + y) 2;;")

let test_nonlocal _ =
  assert_equal "| | (| | 1 + | 2)" (pau "(fun x -> (fun y -> x + y) 2) 1;;");
  assert_equal "| (| | 1 + | 2)" (pau "((fun x -> fun y -> x + y) 1) 2;;")

let _test_stub _ =
  assert_equal "TODO"
    (pau
       "let id = fun self -> fun n -> if n = 0 then 0 else 1 + self self (x - \
        1) in id id 10;;")

let pa_tests =
  [ "Basics" >:: test_basics; "Non-local variable lookup" >:: test_nonlocal ]

let tests = "Program analysis tests" >::: pa_tests

let () =
  Tests_prop.run ();
  run_test_tt_main tests
