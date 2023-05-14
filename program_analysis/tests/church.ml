open OUnit2
open Utils

let zero = "(fun f -> fun x -> x)"
let one = "(fun f -> f)"
let succ = "(fun c -> fun f -> fun x -> f (c f x))"
let add = "(fun m -> fun n -> fun f -> fun x -> m f (n f x))"
let mul = "(fun m -> fun n -> fun f -> fun x -> m (n f) x)"
let unchurch = "(fun f -> f (function x -> x + 1) 0)"

let test_church _ =
  assert_equal "(0 + 1)" (pau (unchurch ^ "(" ^ add ^ zero ^ one ^ ");;"))
