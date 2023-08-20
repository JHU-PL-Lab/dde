[@@@warning "-32"]

open OUnit2
open Core
open Utils
open Test_cases

let gen_test ls =
  List.iter ls ~f:(fun f ->
      let expected, actual = f () in
      assert_equal ~printer:Fn.id expected actual)

let basic_thunked =
  [
    (fun _ -> ("1", pau ~test_num:0 basic.(0)));
    (fun _ -> ("1", pau ~test_num:1 basic.(1)));
    (fun _ -> ("(1 + 2)", pau ~test_num:2 basic.(2)));
  ]

let test_basic _ = gen_test basic_thunked

let nonlocal_lookup_thunked =
  [
    (fun _ -> ("(1 + 2)", pau ~test_num:3 nonlocal_lookup.(0)));
    (fun _ -> ("(1 + 2)", pau ~test_num:4 nonlocal_lookup.(1)));
    (fun _ -> ("((3 + 1) + 2)", pau ~test_num:5 nonlocal_lookup.(2)));
  ]

let test_nonlocal_lookup _ = gen_test nonlocal_lookup_thunked

let local_stitching_thunked =
  [
    (fun _ -> ("((1 + 1) + (1 + 1))", pau ~test_num:6 local_stitching.(0)));
    (fun _ -> ("((0 + 1) + 2)", pau ~test_num:7 local_stitching.(1)));
  ]

(* stack stitching is also needed at Var Local *)
let test_local_stitching _ = gen_test local_stitching_thunked

let conditional_thunked =
  [
    (fun _ -> ("(1 + (10 - 1))", pau ~test_num:8 conditional.(0)));
    (fun _ -> ("1", pau ~test_num:9 conditional.(1)));
    (fun _ -> ("1", pau ~test_num:10 conditional.(2)));
    (fun _ -> ("1", pau ~test_num:11 conditional.(3)));
    (fun _ -> ("false", pau ~test_num:12 conditional.(4)));
  ]

let test_conditional _ = gen_test conditional_thunked

let currying_thunked =
  [
    (fun _ -> ("(2 + 1)", pau ~test_num:13 currying.(0)));
    (fun _ -> ("(2 + 1)", pau ~test_num:14 currying.(1)));
    (fun _ -> ("(1 + 2)", pau ~test_num:15 currying.(2)));
    (fun _ -> ("((2 + 1) + (1 + 2))", pau ~test_num:16 currying.(3)));
    (fun _ ->
      ( "(((((1 + 1) + (1 + 2)) + (1 + 3)) + (1 + 4)) + (1 + 5))",
        pau ~test_num:17 currying.(4) ));
  ]

let test_currying _ = gen_test currying_thunked

(* TODO: add input atom (random integer); check DDSE benchmarks;
   forall x. true *)
(* TODO: use record for variants and other DS: trees, list *)
(* TODO: PL assignment examples, e.g. array multiplications *)
(* TODO: Racket/Van Horn examples *)
let recursion_thunked =
  [
    (fun _ ->
      ("(1 + (1 + (1 + ((1 + stub) | 0))))", pau ~test_num:18 recursion.(0)));
    (* (fun _ ->
            ( "(false or (false or (false or ((false or stub) | true))))",
              pau ~test_num:19 recursion.(1) ));
          (* (fun _ -> ("(1 + (1 + (1 + (1 + stub))))", pau ~test_num:20 recursion.(2))); *)
          (fun _ ->
            ("(1 + (1 + (1 + (0 | (1 + stub)))))", pau ~test_num:21 recursion.(3)));
          (fun _ -> ("0", pau ~test_num:22 recursion.(4)));
          (fun _ -> ("true", pau ~test_num:23 recursion.(5)));
          (* (fun _ -> ("false", pau ~test_num:18 recursion.(6))); *)
          (fun _ -> ("true", pau ~test_num:24 recursion.(7)));
          (fun _ -> ("true", pau ~test_num:25 recursion.(8)));
          (fun _ -> ("1", pau ~test_num:26 recursion.(9)));
          (fun _ -> ("1", pau ~test_num:27 recursion.(10)));
          (fun _ -> ("1", pau ~test_num:28 recursion.(11))); *)
    (fun _ ->
      ( "(((((stub + ((2 | ((2 | (stub - 1)) - 1)) - 2)) | (2 | ((2 | (stub - \
         1)) - 1))) + ((2 | ((2 | (stub - 1)) - 1)) - 2)) + (1 | ((2 | ((2 | \
         (stub - 1)) - 1)) - 2))) + 1)",
        pau ~verify:false ~test_num:29 recursion.(12) ));
  ]

(* (((((stub + ((2 | ((2 | (stub - 1)) - 1)) - 2)) | (2 | ((2 | (stub - 1)) - 1))) + ((2 | ((2 | (stub - 1)) - 1)) - 2)) + (1 | ((2 | ((2 | (stub - 1)) - 1)) - 2))) + 1) *)

let test_recursion _ = gen_test recursion_thunked

let adapted_thunked =
  [
    (fun _ ->
      ( "((3 * (2 * 1)) + (4 * (3 * (2 * (((2 | ((2 | (stub - 1)) - 1)) * \
         stub) | 1)))))",
        pau ~verify:false ~test_num:30 adapted.(0) ));
  ]

let test_adapted _ = gen_test adapted_thunked

let church_basic_thunked =
  [
    (fun _ -> ("(0 + 1)", pau church_basic.(0)));
    (fun _ -> ("((0 + 1) + 1)", pau church_basic.(1)));
    (fun _ -> ("(((0 + 1) + 1) + 1)", pau church_basic.(2)));
    (fun _ -> ("((((0 + 1) + 1) + 1) + 1)", pau church_basic.(3)));
  ]

let test_church_basic _ = gen_test church_basic_thunked
let church_binop_thunked = [ (fun _ -> ("(0 + 1)", pau church_binop.(0))) ]
let test_church_binop _ = gen_test church_binop_thunked

let lists_thunked =
  [
    (* (fun _ -> ("{ hd = 1; tl = {} }", pau lists.(0)));
       (fun _ -> ("2", pau lists.(1)));
       (fun _ -> ("{ hd = 2; tl = { hd = 3; tl = {} } }", pau lists.(2)));
       (fun _ -> ("2", pau lists.(3))); *)
    (fun _ -> ("", pau lists.(4)));
  ]

let test_lists _ = gen_test lists_thunked

let tests_thunked =
  basic_thunked @ nonlocal_lookup_thunked @ local_stitching_thunked
  @ conditional_thunked @ currying_thunked @ recursion_thunked
  @ church_basic_thunked @ church_binop_thunked @ lists_thunked
  @ adapted_thunked

let test_pa =
  [
    (* "Basics" >:: test_basic; *)
    (* "Non-local variable lookup" >:: test_nonlocal_lookup; *)
    (* "Var local stack stitching" >:: test_local_stitching; *)
    (* "Conditional" >:: test_conditional; *)
    (* "Currying" >:: test_currying; *)
    "Recursion" >:: test_recursion;
    (* "Church numerals basics" >:: test_church_basic;
       "Church numerals binary operations" >:: test_church_binop; *)
    (* "Adapted" >:: test_adapted; *)
    (* "Lists" >:: test_lists; *)
  ]

let tests = "Program analysis tests" >::: test_pa

let _ =
  (* Pbt.run _; *)
  let out_file = Out_channel.create "logs" in
  Logs.set_reporter
    (Logs_fmt.reporter ~dst:(Format.formatter_of_out_channel out_file) ());
  Logs.set_level (Some Logs.Info);
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  if !bench then Bench.run tests_thunked;
  run_test_tt_main tests

(* TODO: more tests, more projections than available *)
