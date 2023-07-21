open OUnit2
open Utils
open Test_cases

let test_church_basic _ =
  assert_equal "(0 + 1)" (pau church_basic.(0));
  assert_equal "((0 + 1) + 1)" (pau church_basic.(1));
  assert_equal "(((0 + 1) + 1) + 1)" (pau church_basic.(2));
  assert_equal "((((0 + 1) + 1) + 1) + 1)" (pau church_basic.(3))

let test_church_binop _ = assert_equal "(0 + 1)" (pau church_binop.(0))

(* assert_equal "TODO"
   (pau (unchurch ^ "(" ^ add ^ church 20 ^ church 10 ^ ");;")) *)
(* assert_equal "TODO"
   (pau (unchurch ^ "(" ^ mul ^ church 3 ^ church 2 ^ ");;")) *)

let test_church =
  [
    "Church numerals basics" >:: test_church_basic;
    "Church numerals binary operations" >:: test_church_binop;
  ]
