open OUnit2

let tests =
  "All tests"
  >::: [ Tests_subst.dde_subst; Tests_env.dde_env; Tests_self.dde_self ]

let () = run_test_tt_main tests
