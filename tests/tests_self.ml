open OUnit2
open Utils
open Fbast

let test_laziness _ =
  assert_equal
    (dde_eval "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3));;")
    (dde_parse "fun y -> (fun z -> z + 1) (1 + 2 + 3)")

let dde_self_tests = [ "Laziness" >:: test_laziness ]
let dde_self = "DDE against self" >::: dde_self_tests