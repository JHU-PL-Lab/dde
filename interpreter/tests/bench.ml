open Utils
open Core_bench

let fib_bench () =
  Command_unix.run ~argv:[ "" ]
    (Bench.make_command
       [
         Bench.Test.create ~name:"fib 25" (fun () -> ());
         Bench.Test.create ~name:"fib 50" (fun () -> ());
         Bench.Test.create ~name:"fib 75" (fun () -> ());
         Bench.Test.create ~name:"fib 100" (fun () -> ());
       ])
