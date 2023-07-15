open OUnit2

let msg = "FAILED TO VERIFY"
let verify_result test = assert_bool msg (Utils.verify_result test)

let verify_basic _ =
  verify_result Test_cases.basic.(0);
  verify_result Test_cases.basic.(1)

let verify_nonlocal_lookup _ =
  verify_result Test_cases.nonlocal_lookup.(0);
  verify_result Test_cases.nonlocal_lookup.(1);
  verify_result Test_cases.nonlocal_lookup.(2)

let verify_local_stitching _ =
  verify_result Test_cases.local_stitching.(0);
  verify_result Test_cases.local_stitching.(1)

let verify_conditional _ =
  verify_result Test_cases.conditional.(0);
  verify_result Test_cases.conditional.(1);
  verify_result Test_cases.conditional.(2)

let verify_currying _ =
  verify_result Test_cases.currying.(0);
  verify_result Test_cases.currying.(1);
  verify_result Test_cases.currying.(2);
  verify_result Test_cases.currying.(3);
  verify_result Test_cases.currying.(4)

let verify_recursion _ = verify_result Test_cases.recursion.(0)

let verify_pa =
  [
    "Verify basic" >:: verify_basic;
    "Verify non-local lookup" >:: verify_nonlocal_lookup;
    "Verify local stitching" >:: verify_local_stitching;
    "Verify conditional" >:: verify_conditional;
    "Verify currying" >:: verify_currying;
    "Verify recursion" >:: verify_recursion;
  ]
