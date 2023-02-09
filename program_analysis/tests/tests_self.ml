open OUnit2
open Test_utils

let test_basics _ =
  assert_equal "| | 1" (pau "(fun x -> x) 1;;");
  assert_equal "| (1 + | 2)" (pau "(fun y -> 1 + y) 2;;")

let test_nonlocal _ =
  assert_equal "| (| | 1 + | 2)" (pau "((fun x -> fun y -> x + y) 1) 2;;");
  assert_equal "| | (| | 1 + | 2)" (pau "(fun x -> (fun y -> x + y) 2) 1;;")

let pa_self_tests =
  [ "Basics" >:: test_basics; "Non-local variable lookup" >:: test_nonlocal ]

let pa_self = "Program analysis against self" >::: pa_self_tests
