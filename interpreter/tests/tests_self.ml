open OUnit2
open Utils

let assert_equal = assert_equal ~printer:Core.Fn.id

let test_laziness _ =
  assert_equal "{ x = 1 + 1; y = 1 + 1 }"
    (peu "{ x = 1 + 1; y = (fun z -> z + 1) 1 }");
  assert_equal "{ x = 1 }.x" (peu "{ x = 1 }.x");
  assert_equal "{ label = 1 }.x" (peu "{ label = if true then 1 else 0 }.x");
  assert_equal "fun y -> 7"
    (peu ~should_simplify:true
       "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3))");
  assert_equal "fun y -> 1"
    (peu ~should_simplify:true "(fun x -> fun y -> x) (if true then 1 else 0)")

(* let test_memoization _ =
   assert_equal "1" (peu ~should_simplify:true (Tests_subst.dde_fib 1)) *)

let test_record _ =
  (* gives value at leftmost x *)
  assert_equal "1" (peu ~should_simplify:true "{ x = 1; y = 3; x = 2 }.x");
  assert_equal "{ counter = -98; cond = true }"
    (peu ~should_simplify:true
       "let data = { counter = 99; cond = false } in if data.cond then { \
        counter = data.counter + 1; cond = false } else { counter = 1 - \
        data.counter; cond = true }");
  assert_equal "1"
    (peu ~should_simplify:true
       "(fun r -> if green in r then r.green else if blue in r then r.blue \
        else r.red) ({ cyan = 10; blue = 1 })");
  (* lists *)
  (* TODO: more to come *)
  assert_equal "2"
    (peu ~should_simplify:true "{ hd = 1; tl = { hd = 2; tl = {} } }.tl.hd")

let test_letassert _ =
  assert_equal "2" (peu ~should_simplify:true "letassert x = 1 + 1 in x = 2")

let dde_self_tests =
  [
    "Laziness" >:: test_laziness;
    (* "Memoization" >:: test_memoization; *)
    "Record operations" >:: test_record;
    "letassert" >:: test_letassert;
  ]

let dde_self = "DDE against self" >::: dde_self_tests
