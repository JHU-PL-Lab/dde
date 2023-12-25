open Core
open OUnit2

let pau = Pa.Debugutils.pau
let pau' = Simple_pa.Debug_utils.pau
let pau'' = Display_pa.Debugutils.pau

let gen_test ls =
  List.iter ls ~f:(fun f ->
      let expected, actual = f () in
      assert_equal ~printer:Fn.id expected actual)
