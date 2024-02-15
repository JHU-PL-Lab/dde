[@@@warning "-32"]

open OUnit2
open Core
open Core_bench
open Utils

let basic_thunked =
  [
    (fun _ -> ("1", pau "letassert x = 1 in true"));
    (fun _ -> ("1", pau "letassert x = (fun x -> x) 1 in x = 1"));
    (fun _ -> ("3", pau "letassert x = (fun y -> 1 + y) 2 in x = 3"));
  ]

let nonlocal_lookup_thunked =
  [
    (fun _ ->
      ("3", pau "letassert x = (fun x -> (fun y -> x + y) 2) 1 in x = 3"));
    (fun _ ->
      ("3", pau "letassert x = ((fun x -> fun y -> x + y) 1) 2 in x = 3"));
    (fun _ ->
      ( "6",
        pau
          "letassert x = (fun x -> (fun y -> (fun z -> x + y + z) 2) 1) 3 in x \
           = 6" ));
  ]

let local_stitching_thunked =
  [
    (fun _ ->
      ( "4",
        pau
          "letassert x =\n\
           (let add = (fun num -> fun n -> n + num) in\n\
           let add1 = add 1 in\n\
           let add1' = (fun n -> add1 n) in\n\
           add1 1 + add1' 1)\n\
           in x = 4" ));
    (fun _ ->
      ( "3",
        pau
          "letassert x =\n\
           (let add = (fun f -> fun g -> fun x -> f g x) in\n\
           let add1 = add (fun z -> fun n -> z n + 2) in\n\
           let add2 = add1 (fun y -> y + 1) in\n\
           add2 0)\n\
           in x = 3" ));
  ]

let conditional_thunked =
  [
    (fun _ ->
      ( "10",
        pau
          "letassert x = (fun id -> id 10) (fun n -> if n = 0 then 0 else 1 + \
           (n - 1)) in x = 10" ));
    (fun _ -> ("1", pau "letassert x = if true then 1 else 2 in x = 1"));
    (fun _ ->
      ( "1",
        pau
          "letassert x = (fun x -> (if true then (fun y -> y) else (fun z -> \
           z)) x) 1 in x = 1" ));
    (fun _ ->
      ( "1",
        pau
          "letassert x = if true then (if true then (if true then 1 else 2) \
           else 3) else 4 in x = 1" ));
    (fun _ ->
      ( "false",
        pau
          "letassert x = if (if (if true and false then false else true) then \
           false else true) then true else false in not x" ));
  ]

let currying_thunked =
  [
    (fun _ ->
      ( "3",
        pau
          "letassert x = let add = (fun num -> fun n -> n + num) in let add1 = \
           add 1 in add1 2 in x = 3" ));
    (fun _ ->
      ( "3",
        pau
          "letassert x = (fun add -> (fun add1 -> (fun add2 -> add1 2) (add \
           2)) (add 1)) (fun num -> fun n -> n + num) in x = 3" ));
    (fun _ ->
      ( "3",
        pau
          "letassert x = let add = (fun num -> fun n -> n + num) in let add2 = \
           add 2 in add2 1 in x = 3" ));
    (fun _ ->
      ( "6",
        pau
          "letassert x = let add = (fun num -> fun n -> n + num) in let add1 = \
           add 1 in let add2 = add 2 in add1 2 + add2 1 in x = 6" ));
    (fun _ ->
      ( "20",
        pau
          "letassert x =\n\
           let add = (fun num -> fun n -> n + num) in\n\
           let add1 = add 1 in\n\
           let add2 = add 2 in\n\
           let add3 = add 3 in\n\
           let add4 = add 4 in\n\
           let add5 = add 5 in\n\
           add1 1 + add2 1 + add3 1 + add4 1 + add5 1 in\n\
           x = 20" ));
  ]

let recursion_aux1 =
  "let f = fun self -> fun x -> (fun y -> if x and y then true else if x and \
   not y then not (self self true true) else if not x and y then self self \
   true false else self self false true) in f f"

let recursion_aux2 =
  "let f = (fun x -> fun dummy -> x) in let loop = (fun self -> fun x -> let r \
   = (f x) in if x = 1 then (r 1) else if x = 0 then (self self 1) else (self \
   self 0)) in loop loop"

let recursion_thunked =
  [
    (fun _ ->
      ( "((3 + ((1 + stub) | 0)) | 2)",
        pau ~name:"id"
          "letassert x = let id = fun self -> fun n -> if n = 0 then 0 else 1 \
           + self self (n - 1) in id id 10 in x >= 2" ));
    (fun _ ->
      ( "(3 + (1 + stub))",
        pau ~name:"id_diverge"
          "letassert _ = let id = fun self -> fun n -> if n = 0 then 0 else 1 \
           + self self (n - 1) in id id (-1) in false" ));
    (fun _ ->
      ( "(2 | (3 + (0 | (1 + stub))))",
        pau ~name:"id_alt"
          "letassert x = let id = fun self -> fun n -> if n > 0 then 1 + self \
           self (n - 1) else 0 in id id 10 in x >= 2" ));
    (fun _ ->
      ( "(2 + ((1 + stub) | 0))",
        pau ~name:"id_abs"
          "letassert x = let id = fun self -> fun n -> if n = 0 then 0 else 1 \
           + (fun _ -> self self (n - 1)) 0 in id id 10 in x >= 2" ));
    (fun _ ->
      ( "stub",
        pau ~name:"omega"
          "letassert _ = ((fun self -> fun n -> self self n) (fun self -> fun \
           n -> self self n) 0) in false" ));
    (fun _ ->
      ( "true",
        pau
          "letassert x = let f = (fun x -> (fun y -> y) x) in let repeat = fun \
           self -> fun acc -> if acc then true else self self (self self (f \
           true)) in repeat repeat true in x" ));
    (fun _ ->
      ( "true",
        pau
          "letassert x = let f = (fun x -> fun dummy -> x) in let loop = fun \
           self -> fun x -> let r = (f x) in if x then r 0 else (self self \
           true) in (loop loop false) in x" ));
    (fun _ ->
      ("true", pau ("letassert x = " ^ recursion_aux1 ^ " true true in x")));
    (fun _ ->
      ("false", pau ("letassert x = " ^ recursion_aux1 ^ " true false in not x")));
    (fun _ -> ("1", pau ("letassert x = " ^ recursion_aux2 ^ " 0 in x >= 1")));
    (fun _ -> ("1", pau ("letassert x = " ^ recursion_aux2 ^ " 1 in x >= 1")));
    (fun _ ->
      ("1", pau ("letassert x = " ^ recursion_aux2 ^ " (0 - 1) in x >= 1")));
    (fun _ ->
      ( "((((2 | (stub - 1)) - 1) + (0 | (((2 | (stub - 1)) - 1) - 2))) + 1)",
        pau
          "let fib = fun self -> fun n -> if n <= 1 then n else self self (n - \
           1) + self self (n - 2) in fib fib 3" ));
    (fun _ ->
      ( "(0 | 1)",
        pau
          "letassert x = let nonsense = fun self -> fun n -> if (self self n) \
           = 0 then 1 else 0 in nonsense nonsense 0 in x >= 0" ));
  ]

let church0 = "(fun f0 -> fun x0 -> x0)"
let church1 = "(fun f1 -> fun x1 -> f1 x1)"
let church2 = "(fun f2 -> fun x2 -> f2 (f2 x2))"
let church3 = "(fun f3 -> fun x3 -> f3 (f3 (f3 x3)))"
let succ = "(fun c -> fun f -> fun x -> f (c f x))"
let plus = "(fun m -> fun n -> fun f -> fun x -> m f (n f x))"
let mult = "(fun m -> fun n -> fun f -> m (n f))"
let unchurch = "(fun f -> f (function x -> x + 1) 0)"

let church n =
  let rec aux n =
    match n with 0 -> church0 | n -> succ ^ "(" ^ aux (n - 1) ^ ")"
  in
  "(" ^ aux n ^ ")"

let church_thunked =
  [
    (fun _ -> ("1", pau ("letassert x = " ^ unchurch ^ church 1 ^ " in x = 1")));
    (fun _ -> ("2", pau ("letassert x = " ^ unchurch ^ church 2 ^ " in x = 2")));
    (fun _ -> ("3", pau ("letassert x = " ^ unchurch ^ church 3 ^ " in x = 3")));
    (fun _ -> ("4", pau ("letassert x = " ^ unchurch ^ church 4 ^ " in x = 4")));
    (fun _ ->
      ( "1",
        pau
          ("letassert x = " ^ unchurch ^ "(" ^ plus ^ church0 ^ church1
         ^ ") in x = 1") ));
    (fun _ ->
      ( "8",
        pau
          (Format.sprintf "letassert x = %s (%s (%s %s %s) (%s %s %s)) in x = 8"
             unchurch plus mult church2 church1 mult church2 church3) ));
  ]

let list_cons = "(fun x -> fun ls -> { hd = x; tl = ls })"

let list_incr =
  "let incr = fun self -> fun ls -> { hd = (ls.hd) + 1; tl = if hd in (ls.tl) \
   then self self (ls.tl) else {} } in incr incr"

let incr_cell =
  "let incr = fun self -> fun ls -> fun n -> if n = 0 then ls else self self \
   ({ hd = ls.hd + 1; tl = {} }) (n - 1) in incr incr"

let lists_thunked =
  [
    (fun _ ->
      ("1", pau ("letassert x = (" ^ list_cons ^ " 1 ({})).hd" ^ " in x = 1")));
    (fun _ ->
      ( "2",
        pau "letassert x = let ls = { x = 1; y = 2; z = 3 } in ls.y in x = 2" ));
    (fun _ ->
      ( "2",
        pau
          "letassert x = ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = {} } } \
           }.tl.hd) in x = 2" ));
    (fun _ ->
      ( "((stub | { hd = (((stub.hd) + 1) | 2); tl = {} }) | { hd = \
         (((stub.hd) + 1) | 2); tl = {} })",
        pau (incr_cell ^ " ({ hd = 0; tl = {} }) 3") ));
    (fun _ ->
      ("{ hd = 2; tl = {} }", pau (list_incr ^ " ({ hd = 1; tl = {} })")));
    (fun _ ->
      ( "{ hd = 2; tl = { hd = 3; tl = {} } }",
        pau (list_incr ^ " ({ hd = 1; tl = { hd = 2; tl = {} } })") ));
    (fun _ ->
      ( "{ hd = 2; tl = { hd = 3; tl = { hd = 4; tl = {} } } }",
        pau
          (list_incr
         ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = {} } } })") ));
    (fun _ ->
      ( "{ hd = 2; tl = { hd = 3; tl = { hd = (4 | 5); tl = ({ hd = (4 | 5); \
         tl = (stub | {}) } | {}) } } }",
        pau
          (list_incr
         ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = {} } \
            } } })") ));
    (fun _ ->
      ( "{ hd = 2; tl = { hd = 3; tl = { hd = (4 | 5); tl = { hd = (4 | 5); tl \
         = stub } } } }",
        pau
          (list_incr
         ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = { hd \
            = 5; tl = {} } } } } })") ));
  ]

let factorial_thunked =
  [
    (fun _ ->
      ( "(90 * ((((9 | (stub - 1)) - 1) * ((((9 | (stub - 1)) - 1) * stub) | \
         1)) | 1))",
        pau ~name:"fact_10"
          "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
           (n - 1) in fact fact 10" ));
    (fun _ ->
      ( "(380 * ((((19 | (stub - 1)) - 1) * ((((19 | (stub - 1)) - 1) * stub) \
         | 1)) | 1))",
        pau ~name:"fact_20"
          "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
           (n - 1) in fact fact 20" ));
    (fun _ ->
      ( "(1560 * ((((39 | (stub - 1)) - 1) * ((((39 | (stub - 1)) - 1) * stub) \
         | 1)) | 1))",
        pau ~name:"fact_40"
          "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
           (n - 1) in fact fact 40" ));
    (fun _ ->
      ( "(3540 * ((((59 | (stub - 1)) - 1) * ((((59 | (stub - 1)) - 1) * stub) \
         | 1)) | 1))",
        pau ~name:"fact_60"
          "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
           (n - 1) in fact fact 60" ));
    (fun _ ->
      ( "(9900 * ((((99 | (stub - 1)) - 1) * ((((99 | (stub - 1)) - 1) * stub) \
         | 1)) | 1))",
        pau ~name:"fact_100"
          "let fact = fun self -> fun n -> if n = 0 then 1 else n * self self \
           (n - 1) in fact fact 100" ));
  ]

(*
  DDPA tests run with the full analysis.
  In order to include a test in the benchmark, its format must be (name, fun _ -> ...).
*)
let ddpa_thunked =
  [
    ("blur", fun _ -> ("true", pau ~name:"blur" (read_case "blur.ml")));
    ("eta", fun _ -> ("false", pau ~name:"eta" (read_case "eta.ml")));
    ( "facehugger",
      fun _ ->
        ( "((6 * 1) + (12 * ((((3 | (stub - 1)) - 1) * ((((3 | (stub - 1)) - \
           1) * stub) | 1)) | 1)))",
          pau ~name:"facehugger" (read_case "facehugger.ml") ) );
    ("kcfa-2", fun _ -> ("false", pau ~name:"kcfa-2" (read_case "kcfa-2.ml")));
    ("kcfa-3", fun _ -> ("false", pau ~name:"kcfa-3" (read_case "kcfa-3.ml")));
    ( "loop2-1",
      fun _ ->
        ( "((stub | ((stub | stub) | (((stub | ((0 | stub) + (10 | (9 | (stub \
           - 1))))) + (10 | (9 | (stub - 1)))) | ((0 | stub) + (10 | (9 | \
           (stub - 1))))))) | ((stub | ((stub | stub) | (((stub | ((0 | stub) \
           + (10 | (9 | (stub - 1))))) + (10 | (9 | (stub - 1)))) | ((0 | \
           stub) + (10 | (9 | (stub - 1))))))) | (((stub | (stub | (((stub | \
           ((0 | stub) + (10 | (9 | (stub - 1))))) + (10 | (9 | (stub - 1)))) \
           | ((0 | stub) + (10 | (9 | (stub - 1))))))) | (stub | (((stub | ((0 \
           | stub) + (10 | (9 | (stub - 1))))) + (10 | (9 | (stub - 1)))) | \
           ((0 | stub) + (10 | (9 | (stub - 1))))))) | (((0 | (((stub | stub) \
           + (10 | (9 | (stub - 1)))) | stub)) + (10 | (9 | (stub - 1)))) | \
           (((((0 | (((stub | stub) + (10 | (9 | (stub - 1)))) | stub)) + (10 \
           | (9 | (stub - 1)))) | stub) + (10 | (9 | (stub - 1)))) | ((((0 | \
           (stub | (stub + (10 | (9 | (stub - 1)))))) + (10 | (9 | (stub - \
           1)))) | (stub + (10 | (9 | (stub - 1))))) + (10 | (9 | (stub - \
           1)))))))))",
          (* "((stub | (stub | (((stub | stub) + (10 | (9 | (stub - 1)))) | \
             stub))) | ((stub | (stub | (((stub | stub) + (10 | (9 | (stub - \
             1)))) | stub))) | (((stub | (stub | (((stub | stub) + (10 | (9 | \
             (stub - 1)))) | stub))) | (stub | (((stub | stub) + (10 | (9 | \
             (stub - 1)))) | stub))) | ((((((0 | (((stub | stub) + (10 | (9 | \
             (stub - 1)))) | stub)) + (10 | (9 | (stub - 1)))) | stub) + (10 | \
             (9 | (stub - 1)))) | ((stub | stub) + (10 | (9 | (stub - 1))))) | \
             stub))))", *)
          pau ~name:"loop2-1" (read_case "loop2-1.ml") ) );
    (* ("loop2-1'", fun _ -> ("", pau ~name:"loop2-1'" (read_case "loop2-1'.ml"))); *)
    ("mj09", fun _ -> ("2", pau ~name:"mj09" (read_case "mj09.ml")));
    ( "map",
      fun _ ->
        ( "{ hd = 8; tl = { hd = 9; tl = ({ hd = (9 | 10); tl = ({ hd = (9 | \
           10); tl = stub } | {}) } | {}) } }",
          pau ~name:"map" (read_case "map.ml") ) );
    ("primtest", fun _ -> ("15", pau ~name:"primtest" (read_case "primtest.ml")));
    ("rsa", fun _ -> ("false", pau ~name:"rsa" (read_case "rsa.ml")));
  ]

(* Long-running DDPA tests *)

let ddpa_sat1_thunked =
  ( "sat-1",
    fun _ -> ("(false | true)", pau ~name:"sat-1" (read_case "sat-1.ml")) )

let ddpa_sat2_thunked =
  ( "sat-2",
    fun _ -> ("(false | true)", pau ~name:"sat-2" (read_case "sat-2.ml")) )

let ddpa_sat3_thunked =
  ( "sat-3",
    fun _ -> ("(false | true)", pau ~name:"sat-3" (read_case "sat-3.ml")) )

let ddpa_ack_thunked =
  ("ack", fun _ -> ("", pau ~name:"ack" (read_case "ack.ml")))

let ddpa_tak_thunked =
  ("tak", fun _ -> ("", pau ~name:"tak" (read_case "tak.ml")))

let ddpa_cpstak_thunked =
  ("cpstak", fun _ -> ("", pau ~name:"cpstak" (read_case "cpstak.ml")))

(* DDPA tests run with the simple analysis. *)
let ddpa_simple_thunked =
  [
    (* ( "blur (simple)",
         fun _ -> ("false | true", pau' ~name:"blur" (read_case "blur.ml")) );
       ("eta (simple)", fun _ -> ("false", pau' ~name:"eta" (read_case "eta.ml")));
       ( "facehugger (simple)",
         fun _ -> ("Int", pau' ~name:"facehugger" (read_case "facehugger.ml")) );
       ( "kcfa-2 (simple)",
         fun _ -> ("false", pau' ~name:"kcfa-2" (read_case "kcfa-2.ml")) );
       ( "kcfa-3 (simple)",
         fun _ -> ("false", pau' ~name:"kcfa-3" (read_case "kcfa-3.ml")) ); *)
    ( "loop2-1 (simple)",
      fun _ ->
        ( "Int | stub | stub | stub | stub | stub | stub | stub | stub",
          (* "Int | stub | stub | stub | stub | stub", *)
          pau' ~name:"loop2-1" (read_case "loop2-1.ml") ) );
    (* ("mj09 (simple)", fun _ -> ("Int", pau' ~name:"mj09" (read_case "mj09.ml")));
       ( "map (simple)",
         fun _ ->
           ( "{ hd = Int; tl = { hd = Int; tl = {} | { hd = Int; tl = {} | { hd = \
              Int; tl = stub } } } }",
             pau' ~name:"map" (read_case "map.ml") ) );
       ( "primtest (simple)",
         fun _ -> ("Int | stub", pau' ~name:"primtest" (read_case "primtest.ml"))
       );
       ( "rsa (simple)",
         fun _ -> ("false | true", pau' ~name:"rsa" (read_case "rsa.ml")) ); *)
    (* ( "sat-1 (simple)",
       fun _ -> ("false | true", pau' ~name:"sat-1" (read_case "sat-1.ml")) ); *)
    (* ( "sat-2 (simple)",
         fun _ -> ("false | true", pau' ~name:"sat-2" (read_case "sat-2.ml")) );
       ( "sat-3 (simple)",
         fun _ -> ("false | true", pau' ~name:"sat-3" (read_case "sat-3.ml")) );
       ( "sat-5 (simple)",
         fun _ -> ("true", pau' ~name:"sat-5" (read_case "sat-5.ml")) ); *)
  ]

let ddpa_ack_simple_thunked =
  ("ack", fun _ -> ("Int | 2", pau' ~name:"ack" (read_case "ack.ml")))

let ddpa_tak_simple_thunked =
  ("tak", fun _ -> ("15", pau' ~name:"tak" (read_case "tak.ml")))

let ddpa_cpstak_simple_thunked =
  ( "cpstak",
    fun _ ->
      ( "15 | 18 | 31 | 32 | stub | stub | stub | stub",
        pau' ~name:"cpstak" (read_case "cpstak.ml") ) )

(* Modify me to define custom tests *)
let custom_thunked =
  [
    (* Run with full analysis *)
    (fun _ ->
      ( "expected test result",
        pau ~name:"your_test_name" (read_case "your_test.ml") ));
    (* Run with simple analysis *)
    (fun _ ->
      ( "expected test result",
        pau' ~name:"your_test_name" (read_case "your_test.ml") ));
  ]

let custom_benchmarkable_thunked =
  [
    (* You must provide the name of the test twice
       as follows to create a test that can be benchmarked *)
    ( "your test name",
      fun _ ->
        ( "expected test result",
          pau ~name:"your_test_name" (read_case "your_test.ml") ) );
  ]

let test_basic _ = gen_test_list basic_thunked
let test_nonlocal_lookup _ = gen_test_list nonlocal_lookup_thunked
let test_local_stitching _ = gen_test_list local_stitching_thunked
let test_conditional _ = gen_test_list conditional_thunked
let test_currying _ = gen_test_list currying_thunked
let test_recursion _ = gen_test_list recursion_thunked
let test_church _ = gen_test_list church_thunked
let test_lists _ = gen_test_list lists_thunked
let test_factorial _ = gen_test_list factorial_thunked

(* Benchmarkable tests use `gen_labeled_test(_list)` instead of `gen_test_list` *)
let test_ddpa _ = gen_labeled_test_list ddpa_thunked
let test_ddpa_sat1 _ = gen_labeled_test ddpa_sat1_thunked
let test_ddpa_sat2 _ = gen_labeled_test ddpa_sat2_thunked
let test_ddpa_sat3 _ = gen_labeled_test ddpa_sat3_thunked
let test_ddpa_ack _ = gen_labeled_test ddpa_ack_thunked
let test_ddpa_tak _ = gen_labeled_test ddpa_tak_thunked
let test_ddpa_cpstak _ = gen_labeled_test ddpa_cpstak_thunked
let test_ddpa_simple _ = gen_labeled_test_list ddpa_simple_thunked
let test_ddpa_ack_simple _ = gen_labeled_test ddpa_ack_simple_thunked
let test_ddpa_tak_simple _ = gen_labeled_test ddpa_tak_simple_thunked
let test_ddpa_cpstak_simple _ = gen_labeled_test ddpa_cpstak_simple_thunked
let test_custom _ = gen_test_list custom_thunked

let test_custom_benchmarkable _ =
  gen_labeled_test_list custom_benchmarkable_thunked

let tests =
  "Pure demand program analysis tests"
  >::: [
         (* "Basics" >:: test_basic;
            "Non-local variable lookup" >:: test_nonlocal_lookup;
            "Var local stack stitching" >:: test_local_stitching;
            "Conditional" >:: test_conditional;
            "Currying" >:: test_currying;
            "Recursion" >:: test_recursion;
            "Church numerals" >:: test_church;
            "Lists" >:: test_lists;
            "Factorial" >:: test_factorial; *)
         (* "DDPA" >: test_medium test_ddpa; *)
         (* Times out after 10 minutes *)
         (* "DDPA sat-1 (long-running)" >: test_long test_ddpa_sat1; *)
         (* "DDPA sat-2 (long-running)" >: test_long test_ddpa_sat2; *)
         (* "DDPA sat-3 (long-running)" >: test_long test_ddpa_sat3; *)
         (* "DDPA ack (long-running)" >: test_long test_ddpa_ack; *)
         (* "DDPA tak (long-running)" >: test_long test_ddpa_tak; *)
         (* "DDPA cpstak (long-running)" >: test_long test_ddpa_cpstak; *)
         "DDPA (simple)" >: test_medium test_ddpa_simple;
         (* Times out after 10 minutes *)
         (* "DDPA ack (simple, long-running)" >: test_long test_ddpa_ack_simple; *)
         (* "DDPA tak (simple, long-running)" >: test_long test_ddpa_tak_simple; *)
         (* "DDPA cpstak (simple, long-running)"
            >: test_long test_ddpa_cpstak_simple; *)
         (* Uncomment the following to run custom tests *)
         (* "Custom" >: test_long test_custom; *)
         (* "Custom benchmarkable" >: test_long test_custom_benchmarkable; *)
       ]

(*
  Specify benchmarked tests here.
  Uncomment to benchmark custom tests.
*)
let to_benchmark = ddpa_thunked @ ddpa_simple_thunked
(* @ custom_benchmarkable_thunked *)

let benchmark tests =
  Command_unix.run ~argv:[ "" ]
    (Bench.make_command
       (List.map tests ~f:(fun (name, f) -> Bench.Test.create ~name f)))

let enable_logging log_file =
  let dst = log_file |> Out_channel.create |> Format.formatter_of_out_channel in
  Logs.set_reporter (Logs_fmt.reporter ~dst ~pp_header:(fun _ _ -> ()) ());
  Logs.set_level (Some Logs.Debug)

let _ =
  Arg.parse
    [
      ("--log", Arg.Unit (fun _ -> enable_logging "logs"), "Log to default file");
      ("-log", Arg.String enable_logging, "Log to custom file");
      ( "--runtime",
        Arg.Unit
          (fun _ ->
            Pa.Debug_utils.report_runtime := true;
            Simple_pa.Debug_utils.report_runtime := true),
        "Report runtime (processor time)" );
      ( "--no-cache",
        Arg.Unit
          (fun _ ->
            Pa.Debug_utils.caching := false;
            Simple_pa.Debug_utils.caching := false),
        "Turn off caching" );
      ( "--verify",
        Arg.Unit (fun _ -> Pa.Debug_utils.verify := true),
        "Enable Z3 verification of final analysis result" );
      ( "--graph",
        Arg.Unit (fun _ -> Pa.Debug_utils.graph := true),
        "Visualize final result" );
      ("--bench", Arg.Unit (fun _ -> benchmark to_benchmark), "Run benchmarks");
    ]
    Fn.ignore "Pure demand program analysis tests";

  run_test_tt_main tests
