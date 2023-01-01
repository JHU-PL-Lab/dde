open OUnit2

let tests =
  "All tests"
  >::: [ Tests_subst.dde_subst; Tests_env.dde_env; Tests_self.dde_self ]

let () =
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  if !bench then Benchmarks.fib_bench ();
  run_test_tt_main tests
