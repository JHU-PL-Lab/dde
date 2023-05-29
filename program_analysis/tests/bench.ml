open Core
open Core_bench
open Utils

let run tests =
  Command_unix.run ~argv:[ "" ]
    (Bench.make_command
       (List.mapi tests ~f:(fun i f ->
            Bench.Test.create ~name:(string_of_int i) f)))
