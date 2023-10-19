open Utils
open Core_bench

let fib =
  Format.sprintf
    "let fib = (fun self -> fun n -> if n = 0 or n = 1 then n else self self \
     (n - 1) + self self (n - 2)) in fib fib %d"

(* TODO: mutable vs immutable data structures *)
(* TODO: use programs from FPSE early assignments *)
(* Benchmark fibonacci to see that it's linear time as intermediate interpretation results are cached *)
let fib_bench () =
  Command_unix.run ~argv:[ "" ]
    (Bench.make_command
       [
         Bench.Test.create ~name:"fib 25" (fun () -> dde_eval_fb (fib 25));
         Bench.Test.create ~name:"fib 50" (fun () -> dde_eval_fb (fib 50));
         Bench.Test.create ~name:"fib 75" (fun () -> dde_eval_fb (fib 75));
         Bench.Test.create ~name:"fib 100" (fun () -> dde_eval_fb (fib 100));
       ])
