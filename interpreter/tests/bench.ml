open Utils
open Core_bench

(* TODO: mutable vs immutable data structures *)
(* TODO: use programs from FPSE early assignments *)
(* Benchmark fibonacci to see that it's linear time as intermediate interpretation results are cached *)
let fib_bench () =
  Command_unix.run ~argv:[ "" ]
    (Bench.make_command
       [
         Bench.Test.create ~name:"fib 25" (fun () ->
             dde_eval_fb (Tests_subst.dde_fib 25));
         Bench.Test.create ~name:"fib 50" (fun () ->
             dde_eval_fb (Tests_subst.dde_fib 50));
         Bench.Test.create ~name:"fib 75" (fun () ->
             dde_eval_fb (Tests_subst.dde_fib 75));
         Bench.Test.create ~name:"fib 100" (fun () ->
             dde_eval_fb (Tests_subst.dde_fib 100));
       ])
