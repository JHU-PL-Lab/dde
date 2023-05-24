open OUnit2
open Utils

let zero = "(fun f -> fun x -> x)"
let one = "(fun f -> f)"
let succ = "(fun c -> fun f -> fun x -> f (c f x))"
let add = "(fun m -> fun n -> fun f -> fun x -> m f (n f x))"
let mul = "(fun m -> fun n -> fun f -> fun x -> m (n f) x)"
let unchurch = "(fun f -> f (function x -> x + 1) 0)"

let church n =
  let rec aux n =
    match n with 0 -> zero | n -> succ ^ "(" ^ aux (n - 1) ^ ")"
  in
  "(" ^ aux n ^ ")"

let test_church_basic _ =
  assert_equal "(0 + 1)" (pau (unchurch ^ church 1 ^ ";;"));
  assert_equal "((0 + 1) + 1)" (pau (unchurch ^ church 2 ^ ";;"));
  assert_equal "(((0 + 1) + 1) + 1)" (pau (unchurch ^ church 3 ^ ";;"));
  assert_equal "((((0 + 1) + 1) + 1) + 1)" (pau (unchurch ^ church 4 ^ ";;"))

let test_church_binop _ =
  assert_equal "(0 + 1)" (pau (unchurch ^ "(" ^ add ^ zero ^ one ^ ");;"))
(* assert_equal "TODO"
   (pau (unchurch ^ "(" ^ add ^ church 20 ^ church 10 ^ ");;")) *)
(* assert_equal "TODO"
   (pau (unchurch ^ "(" ^ mul ^ church 3 ^ church 2 ^ ");;")) *)

let test_church =
  [
    "Church numerals basics" >:: test_church_basic;
    "Church numerals binary operations" >:: test_church_binop;
  ]
