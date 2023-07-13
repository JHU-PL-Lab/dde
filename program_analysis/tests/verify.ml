open OUnit2
open Utils

let failed = "FAILED TO VERIFY"

let verify_basic _ =
  let test = Test_cases.basic.(0) in
  pf "\nTest 0: %s\n" test;
  assert_bool failed (verify_result (pau' test) []);

  let test = Test_cases.basic.(1) in
  pf "\nTest 1: %s\n" test;
  assert_bool failed (verify_result (pau' test) [])

let verify_conditional _ =
  let test = Test_cases.conditional.(1) in
  pf "\nTest 3: %s\n" test;
  assert_bool failed (verify_result (pau' test) [])

let verify_recursion _ =
  let test = Test_cases.recursion.(0) in
  pf "\nTest 4: %s\n" test;
  assert_bool failed (verify_result (pau' test) [])

let verify_pa =
  [
    (* "Verify basic" >:: verify_basic;
       "Verify conditional" >:: verify_conditional; *)
    "Verify recursion" >:: verify_recursion;
  ]

let verification = "Program analysis verification tests" >::: verify_pa
