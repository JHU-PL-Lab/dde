open OUnit2

let tests = "All tests" >::: [ Tests_self.pa_self ]
let () = run_test_tt_main tests
