open OUnit2
open Core
open Church
open Utils
open Test_cases

let gen_test ls =
  List.iter ls ~f:(fun f ->
      let expected, actual = f () in
      assert_equal expected actual)

let basic_thunked =
  [ (fun _ -> ("1", pau basic.(0))); (fun _ -> ("(1 + 2)", pau basic.(1))) ]

let test_basic _ = gen_test basic_thunked

let nonlocal_lookup_thunked =
  [
    (fun _ -> ("(1 + 2)", pau nonlocal_lookup.(0)));
    (fun _ -> ("(1 + 2)", pau nonlocal_lookup.(1)));
    (fun _ -> ("((3 + 1) + 2)", pau nonlocal_lookup.(2)));
  ]

let test_nonlocal_lookup _ = gen_test nonlocal_lookup_thunked

let local_stitching_thunked =
  [
    (fun _ -> ("((1 + 1) + (1 + 1))", pau local_stitching.(0)));
    (fun _ -> ("((0 + 1) + 2)", pau local_stitching.(1)));
  ]

(* stack stitching is also needed at Var Local *)
let test_local_stitching _ = gen_test local_stitching_thunked

let conditional_thunked =
  [
    (fun _ -> ("((10 = 0) = false ⊩ (1 + (10 - 1)))", pau conditional.(0)));
    (fun _ -> ("(true = true ⊩ 1)", pau conditional.(1)));
    (fun _ -> ("1", pau conditional.(2)));
  ]

let test_conditional _ = gen_test conditional_thunked

let currying_thunked =
  [
    (fun _ -> ("(2 + 1)", pau currying.(0)));
    (fun _ -> ("(2 + 1)", pau currying.(1)));
    (fun _ -> ("(1 + 2)", pau currying.(2)));
    (fun _ -> ("((2 + 1) + (1 + 2))", pau currying.(3)));
    (fun _ ->
      ( "(((((1 + 1) + (1 + 2)) + (1 + 3)) + (1 + 4)) + (1 + 5))",
        pau currying.(4) ));
  ]

let test_currying _ = gen_test currying_thunked

let recursion_thunked =
  [
    (fun _ ->
      (* TODO: make more readable *)
      ( "((10 = 0) = false ⊩ (1 + (((10 - 1) = 0) = false ⊩ (1 + ((((10 - 1) - \
         1) = 0) = false ⊩ (1 + ((((10 - 1) - 1) | (((10 - 1) - 1) | (stub - \
         1) - 1) = 0) = false ⊩ (1 + stub)) | ((((10 - 1) - 1) | (((10 - 1) - \
         1) | (stub - 1) - 1) = 0) = true ⊩ 0)))))))",
        pau recursion.(0) ));
  ]

let test_recursion _ = gen_test recursion_thunked

let tests_thunked =
  basic_thunked @ nonlocal_lookup_thunked @ local_stitching_thunked
  @ conditional_thunked @ currying_thunked @ recursion_thunked

let test_pa =
  [
    "Basics" >:: test_basic;
    "Non-local variable lookup" >:: test_nonlocal_lookup;
    "Var local stack stitching" >:: test_local_stitching;
    "If" >:: test_conditional;
    "Currying" >:: test_currying;
    "Recursion" >:: test_recursion;
    "Church numerals" >::: test_church;
  ]

let tests = "Program analysis tests" >::: test_pa

let _ =
  (* Pbt.run _; *)
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  if !bench then Bench.run tests_thunked;
  run_test_tt_main Verify.verification;
  run_test_tt_main tests
