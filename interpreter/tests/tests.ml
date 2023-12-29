open OUnit2

let tests =
  "All tests"
  >::: [
         Tests_subst.dde_subst;
         Tests_env.dde_env;
         Tests_self.dde_self;
         Tests_display.dde_display;
       ]

let () =
  (* let out_file = Core.Out_channel.create "logs" in
     Logs.set_reporter
       (Logs_fmt.reporter ~dst:(Format.formatter_of_out_channel out_file) ());
     Logs.set_level (Some Logs.Debug); *)
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  if !bench then Bench.fib_bench ();
  run_test_tt_main tests
