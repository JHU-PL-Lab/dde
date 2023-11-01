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
    (* (fun _ -> ("1", pau ~test_num:9 conditional.(1))); *)
    (* (fun _ -> ("1", pau ~test_num:10 conditional.(2))); *)
    (* (fun _ -> ("1", pau ~test_num:11 conditional.(3))); *)
    (* (fun _ -> ("false", pau ~test_num:12 conditional.(4))); *)
  ]

let test_conditional _ = gen_test conditional_thunked

let currying_thunked =
  [
    (* (fun _ -> ("(2 + 1)", pau ~test_num:13 currying.(0)));
       (fun _ -> ("(2 + 1)", pau ~test_num:14 currying.(1)));
       (fun _ -> ("(1 + 2)", pau ~test_num:15 currying.(2)));
       (fun _ -> ("((2 + 1) + (1 + 2))", pau ~test_num:16 currying.(3))); *)
    (fun _ ->
      ( "(((((1 + 1) + (1 + 2)) + (1 + 3)) + (1 + 4)) + (1 + 5))",
        pau ~test_num:17 ~verify:false currying.(4) ));
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
      ( "(1 + (1 + ((1 + ((1 + stub) | 0)) | 0)))",
        pau ~test_num:18 ~verify:true recursion.(0) ));
    (* (fun _ ->
         ( "(false or (false or ((false or ((false or stub) | true)) | true)))",
           pau ~test_num:19 ~verify:false recursion.(1) )); *)
    (* TODO: shouldn't have base case *)
    (* (fun _ ->
       ( "(1 + (1 + ((1 + ((1 + stub) | 0)) | 0)))",
         pau ~test_num:20 ~verify:false recursion.(2) )); *)
    (* (fun _ ->
         ( "(1 + (1 + (0 | (1 + (0 | (1 + stub))))))",
           pau ~test_num:21 ~verify:false recursion.(3) ));
       (fun _ -> ("0", pau ~test_num:22 ~verify:false recursion.(4)));
       (fun _ -> ("true", pau ~test_num:23 ~verify:false recursion.(5)));
       (* TODO *)
       (* (fun _ -> ("false", pau ~test_num:18 ~verify:false recursion.(6))); *)
       (fun _ -> ("true", pau ~test_num:24 ~verify:false recursion.(7)));
       (* (fun _ -> ("(false | true)", pau ~test_num:25 ~verify:false recursion.(8))); *)
       (fun _ -> ("(0 | 1)", pau ~test_num:26 ~verify:false recursion.(9)));
       (fun _ -> ("1", pau ~test_num:27 ~verify:false recursion.(10)));
       (fun _ ->
         ("(0 | (1 | (0 - 1)))", pau ~test_num:28 ~verify:false recursion.(11))); *)
    (* (fun _ ->
       ( "((((stub + ((3 | ((3 | (stub - 1)) - 1)) - 2)) | ((3 | (stub - 1)) - \
          1)) + ((3 | ((3 | (stub - 1)) - 1)) - 2)) + (((2 | ((3 | (((3 | \
          ((stub - 1) | (stub - 1))) - 1) | (stub - 1))) - 2)) - 1) + ((2 | \
          (((3 | (((2 | ((stub - 2) | (stub - 2))) - 1) | ((3 | (((2 | ((stub - \
          2) | (stub - 2))) - 1) | (stub - 1))) - 1))) - 2) | (stub - 2))) - \
          2)))",
         pau ~verify:false ~test_num:29 recursion.(12) )); *)
    (* (fun _ ->
       ( "(1 + (1 + ((1 + stub) | 0)))",
         pau ~test_num:30 ~verify:false recursion.(13) )); *)
  ]

let test_recursion _ = gen_test recursion_thunked

let church_basic_thunked =
  [
    (fun _ -> ("(0 + 1)", pau ~test_num:41 church_basic.(0)));
    (fun _ -> ("((0 + 1) + 1)", pau ~test_num:42 church_basic.(1)));
    (fun _ -> ("(((0 + 1) + 1) + 1)", pau ~test_num:43 church_basic.(2)));
    (fun _ -> ("((((0 + 1) + 1) + 1) + 1)", pau ~test_num:44 church_basic.(3)));
  ]

let test_church_basic _ = gen_test church_basic_thunked

let church_binop_thunked =
  [
    (* (fun _ -> ("(0 + 1)", pau ~test_num:45 church_binop.(0))); *)
    (* (fun _ -> ("", pau' ~test_num:45 church_binop.(1))); *)
    (fun _ -> ("", pau ~test_num:45 ~verify:false church_binop.(2)));
    (* (fun _ -> ("", pau ~test_num:45 ~verify:false church_binop.(3))); *)
  ]

let test_church_binop _ = gen_test church_binop_thunked

let lists_thunked =
  [
    (* (fun _ -> ("1", pau' ~test_num:46 lists.(0))); *)
    (* (fun _ -> ("2", pau' ~test_num:47 lists.(1))); *)
    (* (fun _ -> ("2", pau ~test_num:48 ~verify:false lists.(2))); *)
    (fun _ -> ("", pau ~test_num:48 ~verify:false lists.(3)));
    (* (fun _ -> ("", pau' ~test_num:50 ~verify:false lists.(4))); *)
    (* (fun _ -> ("", pau' ~test_num:50 ~verify:false lists.(5))); *)
  ]

let test_lists _ = gen_test lists_thunked

let tests_thunked =
  basic_thunked @ nonlocal_lookup_thunked @ local_stitching_thunked
  @ conditional_thunked @ currying_thunked @ recursion_thunked
  @ church_basic_thunked @ church_binop_thunked @ lists_thunked

let test_prune_d _ =
  let open Dinterp.Ast in
  let open Dinterp.Interp in
  let open Display_pa.Lib in
  (* assert_equal ((0, DNil) => DNil) (prune_d ((0, DNil) => DNil));
     assert_equal
       ((0, (1, DNil) => DNil) => DNil)
       (prune_d ((0, (1, DNil) => DNil) => DNil));
     assert_equal
       ((0, (1, DNil) => DNil) => DNil)
       (prune_d ((0, (1, (2, DNil) => DNil) => DNil) => DNil));
     (* [ 0^[ 1^[ 2 ], 3^[ 3 ] ] ] -> [ 0^[ 1, 3^[ 3 ] ] ] *)
     assert_equal
       ((0, (1, DNil) => ((3, DNil) => DNil)) => DNil)
       (prune_d ((0, (1, (2, DNil) => DNil) => ((3, DNil) => DNil)) => DNil));
     assert_equal true (matches_d ((0, DNil) => DNil) ((1, DNil) => DNil));
     assert_equal true
       (matches_d ((0, DNil) => DNil) ((1, (2, DNil) => DNil) => DNil));
     assert_equal false
       (matches_d ((1, (2, DNil) => DNil) => DNil) ((0, DNil) => DNil)); *)
  assert_equal
    ~printer:(Format.asprintf "%a" Dinterp.Pp.pp_d)
    ((0, (1, DNil) => ((3, DNil) => DNil)) => DNil)
    (prune_d ((0, DNil) => ((1, DNil) => ((2, DNil) => ((3, DNil) => DNil)))))

let ddpa_display_thunked =
  [
    (* (fun _ -> ("true", pau'' (read_input "blur.ml"))); *)
    (* (fun _ -> ("false", pau'' (read_input "eta.ml"))); *)
    (* (fun _ -> ("false", pau'' (read_input "kcfa2.ml"))); *)
    (* (fun _ -> ("false", pau'' (read_input "kcfa3.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "mj09.ml"))); *)
    (* (fun _ ->
       ( "{ hd = Int; tl = { hd = Int; tl = { hd = Int; tl = { hd = Int; tl = \
          stub } | {} } | {} } }",
         pau'' (read_input "map.ml") )); *)
    (* (fun _ -> ("Int", pau'' (read_input "facehugger.ml"))); *)
    (* (fun _ -> ("false | true", pau'' (read_input "sat-1.ml"))); *)
    (fun _ -> ("Int", pau'' (read_input "primtest.ml")));
    (* (fun _ -> ("Int", pau'' (read_input "loop2-1.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "loop2'.ml"))); *)
    (* (fun _ -> ("true", pau'' (read_input "sat-2.ml"))); *)
    (* (fun _ -> ("true", pau'' (read_input "sat-3.ml"))); *)
    (* TODO: loops *)
    (* (fun _ -> ("(false | true)", pau'' (read_input "rsa.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "ack.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "tak.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "fact.ml"))); *)
  ]

let test_ddpa_display _ = gen_test ddpa_display_thunked

let ddpa_thunked =
  [
    (fun _ ->
      ("true", pau ~verify:false ~test_name:"blur" (read_input "blur.ml")));
    (fun _ ->
      ("false", pau ~verify:false ~test_name:"eta" (read_input "eta.ml")));
    (fun _ ->
      ( "((6 * 1) + (12 * ((((3 | (stub - 1)) - 1) * ((((3 | (stub - 1)) - 1) \
         * stub) | 1)) | 1)))",
        pau ~verify:false ~test_name:"facehugger" (read_input "facehugger.ml")
      ));
    (fun _ ->
      ( "(90 * ((((9 | (stub - 1)) - 1) * ((((9 | (stub - 1)) - 1) * stub) | \
         1)) | 1))",
        pau ~verify:false ~test_name:"fact" (read_input "fact.ml") ));
    (fun _ ->
      ("false", pau ~verify:false ~test_name:"kcfa2" (read_input "kcfa2.ml")));
    (fun _ ->
      ("false", pau ~verify:false ~test_name:"kcfa3" (read_input "kcfa3.ml")));
    (fun _ ->
      ( read_output "loop2-1.txt",
        pau ~verify:false ~test_name:"loop2-1" (read_input "loop2-1.ml") ));
    (* (fun _ ->
       ( "((stub | ((stub | stub) | stub)) | ((stub | stub) | stub))",
         pau ~verify:false ~test_name:"loop2'" (read_input "loop2'.ml") )); *)
    (fun _ -> ("2", pau ~verify:false ~test_name:"mj09" (read_input "mj09.ml")));
    (fun _ ->
      ( "{ hd = 8; tl = { hd = 9; tl = ({} | { hd = (9 | 10); tl = ({} | { hd \
         = (9 | 10); tl = stub }) }) } }",
        pau ~verify:false ~test_name:"map" (read_input "map.ml") ));
    (fun _ ->
      ("15", pau ~verify:false ~test_name:"primtest" (read_input "primtest.ml")));
    (fun _ ->
      ( "(false | true)",
        pau ~verify:false ~test_name:"sat-1" (read_input "sat-1.ml") ));
    (fun _ ->
      ( "(false | true)",
        pau ~verify:false ~test_name:"sat-2" (read_input "sat-2.ml") ));
    (fun _ ->
      ( "(false | true)",
        pau ~verify:false ~test_name:"sat-3" (read_input "sat-3.ml") ));
    (fun _ ->
      ("false", pau ~verify:false ~test_name:"rsa" (read_input "rsa.ml")));
    (* (fun _ -> ("Int", pau ~verify:false ~test_name:"ack" (read_input "ack.ml")));
       (fun _ -> ("Int", pau ~verify:false ~test_name:"tak" (read_input "tak.ml")));
       (fun _ ->
         ("", pau ~verify:false ~test_name:"church" (read_input "church.ml")));
       (fun _ ->
         ("", pau ~verify:false ~test_name:"cpstak" (read_input "cpstak.ml"))); *)
  ]

let test_ddpa _ = gen_test ddpa_thunked

let ddpa_simple_thunked =
  [
    (* (fun _ ->
         ( "(false | true)",
           pau' ~verify:false ~test_name:"blur" (read_input "blur.ml") )); *)
    (* (fun _ ->
       ("false", pau' ~verify:false ~test_name:"eta" (read_input "eta.ml"))); *)
    (* (fun _ ->
       ( "Int",
         pau' ~verify:false ~test_name:"facehugger" (read_input "facehugger.ml")
       )); *)
    (* (fun _ ->
       ("false", pau' ~verify:false ~test_name:"kcfa2" (read_input "kcfa2.ml"))); *)
    (* (fun _ ->
       ("false", pau' ~verify:false ~test_name:"kcfa3" (read_input "kcfa3.ml"))); *)
    (fun _ ->
      ( "(Int | (stub | (stub | (stub | (stub | stub)))))",
        pau' ~verify:false ~test_name:"loop2-1" (read_input "loop2-1.ml") ));
    (* (fun _ ->
       ("Int", pau' ~verify:false ~test_name:"mj09" (read_input "mj09.ml"))); *)
    (* (fun _ ->
       ( "{ hd = Int; tl = { hd = Int; tl = ({} | { hd = Int; tl = ({} | { hd = \
          Int; tl = stub }) }) } }",
         pau' ~verify:false ~test_name:"map" (read_input "map.ml") )); *)
    (* (fun _ ->
       ( "stub",
         pau' ~verify:false ~test_name:"primtest" (read_input "primtest.ml") )); *)
    (* (fun _ ->
       ("true", pau' ~verify:false ~test_name:"sat-1" (read_input "sat-1.ml"))); *)
    (* (fun _ ->
       ("true", pau' ~verify:false ~test_name:"sat-2" (read_input "sat-2.ml"))); *)
    (* (fun _ ->
       ("true", pau' ~verify:false ~test_name:"sat-3" (read_input "sat-3.ml"))); *)
    (* (fun _ ->
       ( "(false | true)",
         pau' ~verify:false ~test_name:"rsa" (read_input "rsa.ml") )); *)
    (* (fun _ ->
       ("Int", pau' ~verify:false ~test_name:"ack" (read_input "ack.ml"))); *)
    (* (fun _ ->
       ("Int", pau' ~verify:false ~test_name:"tak" (read_input "tak.ml"))); *)
    (* (fun _ ->
       ("", pau' ~verify:false ~test_name:"cpstak" (read_input "cpstak.ml"))); *)
  ]

let test_ddpa_simple _ = gen_test ddpa_simple_thunked

let test_pa =
  [
    (* "Basics" >:: test_basic;
       "Non-local variable lookup" >:: test_nonlocal_lookup;
       "Var local stack stitching" >:: test_local_stitching;
       "Conditional" >:: test_conditional; *)
    (* "Currying" >:: test_currying; *)
    (* "Recursion" >:: test_recursion; *)
    (* "Church numerals basics" >:: test_church_basic; *)
    (* "Church numerals binary operations" >:: test_church_binop; *)
    (* "Adapted" >:: test_adapted; *)
    (* "Lists" >:: test_lists; *)
    (* "pruned_d" >:: test_prune_d; *)
    "DDPA (simple)"
    >: test_case test_ddpa_simple ~length:(OUnitTest.Custom_length 100000.);
    (* "DDPA" >: test_case test_ddpa ~length:(OUnitTest.Custom_length 100000.); *)
    (* "DDPA (display)"
       >: test_case test_ddpa_display ~length:(OUnitTest.Custom_length 100000.); *)
  ]

let tests = "Program analysis tests" >::: test_pa

let _ =
  (* Pbt.run _; *)
  let out_file = Out_channel.create "logs" in
  Logs.set_reporter
    (Logs_fmt.reporter ~dst:(Format.formatter_of_out_channel out_file) ());
  Logs.set_level (Some Logs.Debug);
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  if !bench then Bench.run tests_thunked;
  run_test_tt_main tests

(* TODO: more tests, more projections than available *)
(* TODO: functions in records (Point, ColorPoint from class), 99 problems OCaml redblack trees *)
