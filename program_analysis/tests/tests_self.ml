open OUnit2
open Test_utils

let test_basics _ = assert_equal "| | 1" (pau "(fun x -> x) 1;;")
let pa_self_tests = [ "Basics" >:: test_basics ]
let pa_self = "Program analysis against self" >::: pa_self_tests
