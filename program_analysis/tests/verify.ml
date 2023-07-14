open OUnit2

let msg = "FAILED TO VERIFY"
let verify_result test = assert_bool msg (Utils.verify_result test)

let verify_basic _ =
  verify_result Test_cases.basic.(0);
  verify_result Test_cases.basic.(1)

let verify_conditional _ =
  verify_result Test_cases.conditional.(0);
  verify_result Test_cases.conditional.(1);
  verify_result Test_cases.conditional.(2)

let verify_recursion _ = verify_result Test_cases.recursion.(0)

let verify_pa =
  [
    "Verify basic" >:: verify_basic;
    "Verify conditional" >:: verify_conditional;
    "Verify recursion" >:: verify_recursion;
  ]

let verification = "Program analysis verification tests" >::: verify_pa
