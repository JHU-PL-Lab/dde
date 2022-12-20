open OUnit2
open Utils
open Core_bench

let test_laziness _ =
  assert_equal
    (dde_eval "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3));;")
    (dde_parse "fun y -> (fun z -> z + 1) (1 + 2 + 3)");
  assert_equal
    (dde_eval "(fun x -> fun y -> x) (if true then 1 else 0);;")
    (dde_parse "fun y -> if true then 1 else 0")

let test_memoization _ =
  assert_equal (dde_eval (Tests_subst.dde_fib 100)) (dde_parse "5050")

(* TODO: mutable vs immutable data structures *)
(* Benchmark fibonacci to see that it's linear time as intermediate interpretation results are cached *)
let fib_bench =
  Command_unix.run
    (Bench.make_command
       [
         Bench.Test.create ~name:"fib 25" (fun () ->
             dde_eval (Tests_subst.dde_fib 100));
         Bench.Test.create ~name:"fib 50" (fun () ->
             dde_eval (Tests_subst.dde_fib 100));
         Bench.Test.create ~name:"fib 75" (fun () ->
             dde_eval (Tests_subst.dde_fib 100));
         Bench.Test.create ~name:"fib 100" (fun () ->
             dde_eval (Tests_subst.dde_fib 100));
       ])

let dde_self_tests =
  [ "Laziness" >:: test_laziness; "Memoization" >:: test_memoization ]

let dde_self = "DDE against self" >::: dde_self_tests
