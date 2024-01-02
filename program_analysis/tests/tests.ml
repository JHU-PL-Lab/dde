[@@@warning "-32"]

open OUnit2
open Core
open Test_cases
open Utils

let basic_thunked =
  [
    (fun _ -> ("1", pau basic.(0)));
    (fun _ -> ("1", pau basic.(1)));
    (fun _ -> ("(1 + 2)", pau basic.(2)));
  ]

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
    (fun _ -> ("(1 + (10 - 1))", pau conditional.(0)));
    (* (fun _ -> ("1", pau  conditional.(1))); *)
    (* (fun _ -> ("1", pau  conditional.(2))); *)
    (* (fun _ -> ("1", pau  conditional.(3))); *)
    (* (fun _ -> ("false", pau  conditional.(4))); *)
  ]

let test_conditional _ = gen_test conditional_thunked

let currying_thunked =
  [
    (* (fun _ -> ("(2 + 1)", pau  currying.(0)));
       (fun _ -> ("(2 + 1)", pau  currying.(1)));
       (fun _ -> ("(1 + 2)", pau  currying.(2)));
       (fun _ -> ("((2 + 1) + (1 + 2))", pau  currying.(3))); *)
    (fun _ ->
      ( "(((((1 + 1) + (1 + 2)) + (1 + 3)) + (1 + 4)) + (1 + 5))",
        pau ~verify:false currying.(4) ));
  ]

let test_currying _ = gen_test currying_thunked

(* TODO: add input atom (random integer); check DDSE benchmarks;
   forall x. true *)
(* TODO: use record for variants and other DS: trees, list *)
(* TODO: PL assignment examples, e.g. array multiplications *)
(* TODO: Racket/Van Horn examples *)
let recursion_thunked =
  [
    (fun _ -> ("(1 + (1 + ((1 + ((1 + stub) | 0)) | 0)))", pau' recursion.(0)));
    (* (fun _ ->
         ( "(false or (false or ((false or ((false or stub) | true)) | true)))",
           pau  ~verify:false recursion.(1) )); *)
    (* TODO: shouldn't have base case *)
    (* (fun _ ->
       ( "(1 + (1 + ((1 + ((1 + stub) | 0)) | 0)))",
         pau  ~verify:false recursion.(2) )); *)
    (* (fun _ ->
         ( "(1 + (1 + (0 | (1 + (0 | (1 + stub))))))",
           pau  ~verify:false recursion.(3) ));
       (fun _ -> ("0", pau  ~verify:false recursion.(4)));
       (fun _ -> ("true", pau  ~verify:false recursion.(5)));
       (* TODO *)
       (* (fun _ -> ("false", pau  ~verify:false recursion.(6))); *)
       (fun _ -> ("true", pau  ~verify:false recursion.(7)));
       (* (fun _ -> ("(false | true)", pau  ~verify:false recursion.(8))); *)
       (fun _ -> ("(0 | 1)", pau  ~verify:false recursion.(9)));
       (fun _ -> ("1", pau  ~verify:false recursion.(10)));
       (fun _ ->
         ("(0 | (1 | (0 - 1)))", pau  ~verify:false recursion.(11))); *)
    (* (fun _ ->
       ( "((((stub + ((3 | ((3 | (stub - 1)) - 1)) - 2)) | ((3 | (stub - 1)) - \
          1)) + ((3 | ((3 | (stub - 1)) - 1)) - 2)) + (((2 | ((3 | (((3 | \
          ((stub - 1) | (stub - 1))) - 1) | (stub - 1))) - 2)) - 1) + ((2 | \
          (((3 | (((2 | ((stub - 2) | (stub - 2))) - 1) | ((3 | (((2 | ((stub - \
          2) | (stub - 2))) - 1) | (stub - 1))) - 1))) - 2) | (stub - 2))) - \
          2)))",
         pau ~verify:false  recursion.(12) )); *)
    (* (fun _ ->
       ( "(1 + (1 + ((1 + stub) | 0)))",
         pau  ~verify:false recursion.(13) )); *)
  ]

let test_recursion _ = gen_test recursion_thunked

let church_basic_thunked =
  [
    (fun _ -> ("(0 + 1)", pau church_basic.(0)));
    (fun _ -> ("((0 + 1) + 1)", pau church_basic.(1)));
    (fun _ -> ("(((0 + 1) + 1) + 1)", pau church_basic.(2)));
    (fun _ -> ("((((0 + 1) + 1) + 1) + 1)", pau church_basic.(3)));
  ]

let test_church_basic _ = gen_test church_basic_thunked

let church_binop_thunked =
  [
    (* (fun _ -> ("(0 + 1)", pau  church_binop.(0))); *)
    (* (fun _ -> ("", pau'  church_binop.(1))); *)
    (fun _ -> ("", pau ~verify:false church_binop.(2)));
    (* (fun _ -> ("", pau  ~verify:false church_binop.(3))); *)
  ]

let test_church_binop _ = gen_test church_binop_thunked

let lists_thunked =
  [
    (* (fun _ -> ("1", pau'  lists.(0))); *)
    (* (fun _ -> ("2", pau'  lists.(1))); *)
    (* (fun _ -> ("2", pau  ~verify:false lists.(2))); *)
    (fun _ -> ("", pau ~verify:false lists.(3)));
    (* (fun _ -> ("", pau'  ~verify:false lists.(4))); *)
    (* (fun _ -> ("", pau'  ~verify:false lists.(5))); *)
  ]

let test_lists _ = gen_test lists_thunked

let test_prune_d _ =
  let open Dinterp.Ast in
  let open Dinterp.Interp in
  let open Display_pa.Lib in
  assert_equal ((0, DNil) => DNil) (prune_d ((0, DNil) => DNil));
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
    (matches_d ((1, (2, DNil) => DNil) => DNil) ((0, DNil) => DNil));
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
    (* (fun _ -> ("(false | true)", pau'' (read_input "rsa.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "ack.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "tak.ml"))); *)
    (* (fun _ -> ("Int", pau'' (read_input "fact.ml"))); *)
  ]

let test_ddpa_display _ = gen_test ddpa_display_thunked

let poly_thunked =
  [
    (* (fun _ ->
       ( "(90 * ((((9 | (stub - 1)) - 1) * ((((9 | (stub - 1)) - 1) * stub) | \
          1)) | 1))",
         pau ~verify:false ~name:"fact 10"
           "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
            (n - 1) in fact fact 10" )); *)
    (* (fun _ ->
       ( "(380 * ((((19 | (stub - 1)) - 1) * ((((19 | (stub - 1)) - 1) * stub) \
          | 1)) | 1))",
         pau ~verify:false ~name:"fact 20"
           "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
            (n - 1) in fact fact 20" )); *)
    (* (fun _ ->
       ( "(1560 * ((((39 | (stub - 1)) - 1) * ((((39 | (stub - 1)) - 1) * stub) \
          | 1)) | 1))",
         pau ~verify:false ~name:"fact 40"
           "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
            (n - 1) in fact fact 40" )); *)
    (* (fun _ ->
       ( "(3540 * ((((59 | (stub - 1)) - 1) * ((((59 | (stub - 1)) - 1) * stub) \
          | 1)) | 1))",
         pau ~verify:false ~name:"fact 60"
           "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
            (n - 1) in fact fact 60" )); *)
    (fun _ ->
      ( "(9900 * ((((99 | (stub - 1)) - 1) * ((((99 | (stub - 1)) - 1) * stub) \
         | 1)) | 1))",
        pau ~verify:false ~name:"fact 100"
          "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
           (n - 1) in fact fact 100" ));
  ]

let test_poly _ = gen_test poly_thunked

let ddpa_thunked =
  [
    (* (fun _ ->
       ("(3 + (1 + stub) | 0) | 2", pau ~verify:false ~name:"id" recursion.(0))); *)
    (* (fun _ -> ("true", pau ~verify:false ~name:"blur" (read_input "blur.ml")));
       (fun _ -> ("false", pau ~verify:false ~name:"eta" (read_input "eta.ml")));
       (fun _ ->
         ( "((6 * 1) + (12 * ((3 | (stub - 1) - 1) * ((3 | (stub - 1) - 1) * \
            stub) | 1) | 1))",
           pau ~verify:false ~name:"facehugger" (read_input "facehugger.ml") ));
       (fun _ ->
         ( "(90 * ((9 | (stub - 1) - 1) * ((9 | (stub - 1) - 1) * stub) | 1) | 1)",
           pau ~verify:false ~name:"fact" (read_input "fact.ml") ));
       (fun _ ->
         ("false", pau ~verify:false ~name:"kcfa2" (read_input "kcfa2.ml")));
       (fun _ ->
         ("false", pau ~verify:false ~name:"kcfa3" (read_input "kcfa3.ml")));
       (fun _ ->
         ( "stub | stub | (stub | stub + 10 | 9 | (stub - 1)) | stub | stub | \
            stub | (stub | stub + 10 | 9 | (stub - 1)) | stub | stub | stub | \
            (stub | stub + 10 | 9 | (stub - 1)) | stub | stub | (stub | stub + 10 \
            | 9 | (stub - 1)) | stub | ((0 | (stub | stub + 10 | 9 | (stub - 1)) \
            | stub + 10 | 9 | (stub - 1)) | stub + 10 | 9 | (stub - 1)) | (stub | \
            stub + 10 | 9 | (stub - 1)) | stub",
           pau ~verify:false ~name:"loop2-1" (read_input "loop2-1.ml") ));
       (fun _ -> ("2", pau ~verify:false ~name:"mj09" (read_input "mj09.ml"))); *)
    (fun _ ->
      ( "{ hd = 8; tl = { hd = 9 | 10; tl = { hd = 9 | 10; tl = { hd = 9 | 10; \
         tl = stub } | {} } | {} } }",
        pau ~verify:false ~name:"map" (read_input "map.ml") ));
    (* (fun _ ->
       ("15", pau ~verify:false ~name:"primtest" (read_input "primtest.ml"))); *)
    (* (fun _ -> ("false", pau ~verify:false ~name:"rsa" (read_input "rsa.ml"))); *)
    (* (fun _ -> ("", pau ~verify:false ~name:"church" (read_input "church.ml"))); *)
    (* (fun _ ->
       ("(false | true)", pau ~verify:false ~name:"sat-1" (read_input "sat-1.ml"))); *)
    (* (fun _ ->
       ("(false | true)", pau ~verify:false ~name:"sat-2" (read_input "sat-2.ml"))); *)
    (* (fun _ ->
       ("(false | true)", pau ~verify:false ~name:"sat-3" (read_input "sat-3.ml"))); *)
    (* (fun _ ->
       ("(false | true)", pau ~verify:false ~name:"sat-5" (read_input "sat-5.ml"))); *)
    (* (fun _ -> ("Int", pau ~verify:false ~name:"ack" (read_input "ack.ml"))); *)
    (* (fun _ -> ("Int", pau ~verify:false ~name:"tak" (read_input "tak.ml"))); *)
    (* (fun _ -> ("", pau ~verify:false ~name:"cpstak" (read_input "cpstak.ml"))); *)
  ]

let test_ddpa _ = gen_test ddpa_thunked

let ddpa_simple_thunked =
  [
    (* (fun _ -> ("Int | 2 | 3", pau' ~name:"id" recursion.(0))); *)
    (* (fun _ -> ("true", pau' ~name:"blur" (read_input "blur.ml")));
       (fun _ -> ("false", pau' ~name:"eta" (read_input "eta.ml")));
       (fun _ ->
         ("Int | 18 | 30", pau' ~name:"facehugger" (read_input "facehugger.ml")));
       (fun _ -> ("false", pau' ~name:"kcfa2" (read_input "kcfa2.ml")));
       (fun _ -> ("false", pau' ~name:"kcfa3" (read_input "kcfa3.ml")));
       (fun _ ->
         ( "Int | 18 | 19 | 20 | stub",
           pau' ~name:"loop2-1" (read_input "loop2-1.ml") ));
       (fun _ -> ("2", pau' ~name:"mj09" (read_input "mj09.ml"))); *)
    (fun _ ->
      ( "{ hd = 8; tl = { hd = 9 | 10; tl = {} | { hd = 9 | 10; tl = {} | { hd \
         = 9 | 10; tl = stub } } } }",
        pau' ~name:"map" (read_input "map.ml") ));
    (* (fun _ -> ("15", pau' ~name:"primtest" (read_input "primtest.ml"))); *)
    (* (fun _ -> ("false", pau' ~name:"rsa" (read_input "rsa.ml"))); *)
    (* (fun _ -> ("false | true", pau' ~name:"sat-1" (read_input "sat-1.ml"))); *)
    (* (fun _ -> ("false | true", pau' ~name:"sat-2" (read_input "sat-2.ml"))); *)
    (* (fun _ -> ("false | true", pau' ~name:"sat-3" (read_input "sat-3.ml"))); *)
    (* (fun _ -> ("false | true", pau' ~name:"sat-4" (read_input "sat-4.ml"))); *)
    (* (fun _ -> ("true", pau' ~name:"sat-5" (read_input "sat-5.ml"))); *)
    (* (fun _ -> ("Int | 2", pau' ~name:"ack" (read_input "ack.ml"))); *)
    (* (fun _ -> ("stub", pau' ~name:"mack" (read_input "mack.ml"))); *)
    (* (fun _ -> ("15", pau' ~name:"tak" (read_input "tak.ml"))); *)
    (* (fun _ ->
       ( "15 | 18 | 31 | 32 | stub | stub | stub | stub",
         pau' ~name:"cpstak" (read_input "cpstak.ml") )); *)
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
    (* "Polynomial" >:: test_poly; *)
    "DDPA (simple)" >: test_long test_ddpa_simple;
    (* "DDPA (full)" >: test_long test_ddpa; *)
    (* "DDPA (display)" >: test_long test_ddpa_display; *)
  ]

let tests_thunked = ddpa_simple_thunked
(* basic_thunked @ nonlocal_lookup_thunked @ local_stitching_thunked
   @ conditional_thunked @ currying_thunked @ recursion_thunked
   @ church_basic_thunked @ church_binop_thunked @ lists_thunked *)

let tests = "Program analysis tests" >::: test_pa

let enable_logging log_file =
  let dst = log_file |> Out_channel.create |> Format.formatter_of_out_channel in
  Logs.set_reporter (Logs_fmt.reporter ~dst ());
  Logs.set_level (Some Logs.Debug)

let _ =
  Arg.parse
    [
      ("--bench", Arg.Unit (fun _ -> Bench.run tests_thunked), "Run benchmarks");
      ("--log", Arg.Unit (fun _ -> enable_logging "logs"), "Log to default file");
      ("-log", Arg.String enable_logging, "Log to custom file");
      ( "--runtime",
        Arg.Unit
          (fun _ ->
            Pa.Debug_utils.report_runtime := true;
            Simple_pa.Debug_utils.report_runtime := true),
        "Report accurate runtime" );
      ( "--no-cache",
        Arg.Unit
          (fun _ ->
            Pa.Debug_utils.caching := false;
            Simple_pa.Debug_utils.caching := false),
        "Turn off caching" );
      (* ("--pbt", Arg.Unit (fun _ -> Pbt.run ()), "Run property-based tests"); *)
    ]
    (fun _ -> ())
    "";

  (* Format.printf "report_runtime: %b\n" !Utils.report_runtime; *)
  run_test_tt_main tests

(* TODO: more tests, more projections than available *)
(* TODO: functions in records (Point, ColorPoint from class), 99 problems OCaml redblack trees *)
