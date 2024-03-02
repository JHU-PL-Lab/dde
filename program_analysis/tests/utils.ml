(** Utilities for testing program analyses *)

open Core
open OUnit2

(** Read a test case file and store content into string *)
let read_case file_name =
  In_channel.read_all
    (Format.sprintf "program_analysis/tests/cases/%s" file_name)

(* Function to execute the full analysis on a program string *)
let pau = Pa.Debug_utils.pau

(* Function to execute the simple analysis on a program string *)
let pau' = Simple_pa.Debug_utils.pau

let gen_test_list ls =
  List.iter ls ~f:(fun f ->
      let expected, actual = f () in
      assert_equal ~printer:Fn.id expected actual)

(** Used to generate tests that can also be benchmarked *)
let gen_labeled_test_list ls =
  List.iter ls ~f:(fun (_, f) ->
      let expected, actual = f () in
      assert_equal ~printer:Fn.id expected actual)

(** Used to generate a test that can also be benchmarked,
    see comments in `tests.ml` for details *)
let gen_labeled_test (_, f) =
  let expected, actual = f () in
  assert_equal ~printer:Fn.id expected actual

(** times out after 5 minutes *)
let test_medium = test_case ~length:(OUnitTest.Custom_length 300.)

(** times out after 10 minutes *)
let test_long = test_case ~length:(OUnitTest.Custom_length 600.)

let test_inf = test_case ~length:(OUnitTest.Custom_length 10_000_000.)
