open OUnit2
open Utils

let verify_basic _ =
  let chcs = pau' Test_cases.basic.(0) in
  assert_bool "BAD" (verify_result chcs [])

let verify_pa = [ "Verify basics" >:: verify_basic ]
let verification = "Program analysis verification tests" >::: verify_pa
