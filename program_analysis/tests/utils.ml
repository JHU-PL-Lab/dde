open Core
open OUnit2

let read_input file_name =
  In_channel.read_all
    (Format.sprintf "program_analysis/tests/cases/%s" file_name)

let pau = Pa.Debug_utils.pau
let pau' = Simple_pa.Debug_utils.pau

let gen_test ls =
  List.iter ls ~f:(fun f ->
      let expected, actual = f () in
      assert_equal ~printer:Fn.id expected actual)

let test_long = test_case ~length:(OUnitTest.Custom_length 90.)
