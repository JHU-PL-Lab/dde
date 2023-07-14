[@@@warning "-26"]

open OUnit2
open Utils
open Program_analysis
open Solver

let msg = "FAILED TO VERIFY"

let verify_basic _ =
  let test = Test_cases.basic.(0) in
  pf "\nTest 1: %s\n" test;
  let chcs, p = pau' test in
  let r = zconst "r" isort in
  let verif = [ r ] |. (p <-- [ r ]) --> (r === zint 1) in
  assert_bool msg (verify_result (verif :: chcs));

  let test = Test_cases.basic.(1) in
  pf "\nTest 2: %s\n" test;
  let chcs, p = pau' test in
  let r = zconst "r" isort in
  let verif = [ r ] |. (p <-- [ r ]) --> (r === zint 3) in
  assert_bool msg (verify_result (verif :: chcs))

let verify_conditional _ =
  let test = Test_cases.conditional.(1) in
  pf "\nTest 3: %s\n" test;
  let chcs, p = pau' test in
  assert_bool msg (verify_result chcs)

let verify_recursion _ =
  let test = Test_cases.recursion.(0) in
  pf "\nTest 4: %s\n" test;
  let chcs, p = pau' test in
  let r = zconst "r" isort in
  let verif = [ r ] |. (p <-- [ r ]) --> (r >== zint 0) in
  assert_bool msg (verify_result (verif :: chcs))

let verify_pa =
  [ (* "Verify basic" >:: verify_basic; *)
    (* "Verify conditional" >:: verify_conditional; *)
    (* "Verify recursion" >:: verify_recursion; *) ]

let verification = "Program analysis verification tests" >::: verify_pa
