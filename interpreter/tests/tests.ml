open OUnit2
open Utils

let test_numerical _ =
  assert_equal "1" (peu "1");
  assert_equal "-2" (peu "-2");
  assert_equal "1 + 2" (peu "1 + 2");
  assert_equal "1 - 2" (peu "1 - 2")

let test_logical _ =
  assert_equal "true" (peu "true");
  assert_equal "false" (peu "false");
  assert_equal "not true" (peu "not true");
  assert_equal "false or true" (peu "false or true");
  assert_equal "true and false" (peu "true and false")

let test_relational _ =
  assert_equal "1 = 1" (peu "1 = 1");
  assert_equal "-1 = 2" (peu "-1 = 2")

let test_let _ =
  assert_equal "false" (peu "let y = false in y");
  assert_equal "5 + 10 = 15" (peu "let x = 5 in let y = 10 in x + y = 15")

let test_if _ =
  assert_equal "1" (peu "if false then 0 else 1");
  assert_equal "1 - 1" (peu "let x = 1 in if x + 2 = 3 then x - 1 else x + 1")

let test_function _ =
  assert_equal "fun x -> x" (peu "fun x -> x");
  assert_equal "fun x -> 1" (peu "fun x -> 1");
  assert_equal "fun x -> fun y -> fun z -> y"
    (peu "fun x -> fun y -> fun z -> y")

let test_basic_application _ =
  assert_equal "1" (peu "(fun x -> x) 1");
  assert_equal "1" (peu "(fun x -> 1) (-2)");
  assert_equal "2" (peu "((fun x -> fun y -> y) 1) 2")

let test_involved_application _ =
  assert_equal "1" (peu "((fun x -> fun y -> x) 1) 2");
  assert_equal "1 + 10" (peu "((fun x -> fun y -> y x) 1) (fun x -> x + 10);");
  assert_equal "6 + 2 + 1"
    (peu "(fun x -> (fun y -> (fun z -> z + 1) y) (x + 2)) 6");
  assert_unequal "fun y -> 1 + 2" (peu "(fun x -> fun y -> x) (1 + 2)")

let dde_ycomb =
  "(fun code -> let repl = (fun self -> fun x -> code (self self) x) in repl \
   repl)"

let dde_fib x =
  Format.sprintf
    "let fib = (fun self -> fun x -> if x = 0 or x = 1 then x else self (x - \
     1) + self (x - 2)) in %s fib %d"
    dde_ycomb x

let test_ycomb _ =
  assert_equal "8" (peu ~simplify:true (dde_fib 6));
  assert_equal "15"
    (peu ~simplify:true
       "let summate0 = fun self -> fun arg -> if arg = 0 then 0 else arg + \
        self self (arg - 1) in summate0 summate0 5")

let test_laziness _ =
  assert_equal "{ x = 1 + 1; y = 1 + 1 }"
    (peu "{ x = 1 + 1; y = (fun z -> z + 1) 1 }");
  assert_equal "1" (peu "{ x = 1 }.x");
  assert_equal "1" (peu "{ label = if true then 1 else 0 }.label");
  assert_equal "fun y -> 7"
    (peu ~simplify:true "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3))");
  assert_equal "fun y -> 1"
    (peu ~simplify:true "(fun x -> fun y -> x) (if true then 1 else 0)")

let test_record _ =
  (* Gives value at leftmost x *)
  assert_equal "1" (peu ~simplify:true "{ x = 1; y = 3; x = 2 }.x");
  assert_equal "{ counter = -98; cond = true }"
    (peu ~simplify:true
       "let data = { counter = 99; cond = false } in if data.cond then { \
        counter = data.counter + 1; cond = false } else { counter = 1 - \
        data.counter; cond = true }");
  assert_equal "1"
    (peu ~simplify:true
       "(fun r -> if green in r then r.green else if blue in r then r.blue \
        else r.red) ({ cyan = 10; blue = 1 })");
  assert_equal "2"
    (peu ~simplify:true "{ hd = 1; tl = { hd = 2; tl = {} } }.tl.hd")

let list_incr =
  "let incr = fun self -> fun ls -> if not (hd in ls) then {} else { hd = \
   (ls.hd) + 1; tl = self self (ls.tl) } in incr incr"

let incr_cell =
  "let incr = fun self -> fun ls -> fun n -> if n = 0 then ls else self self \
   ({ hd = ls.hd + 1; tl = {} }) (n - 1) in incr incr"

let test_record_rec _ =
  assert_equal
    "{ hd = 2; tl = { hd = 3; tl = { hd = 4; tl = { hd = 5; tl = {} } } } }"
    (peu ~simplify:true
       (list_incr
      ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = {} } } \
         } })"));
  assert_equal "{ hd = 5; tl = {} }"
    (peu ~simplify:true (incr_cell ^ " ({ hd = 0; tl = {} }) 5"))

(* Modify me to define custom tests *)
let test_custom _ = assert_equal "expected test result" (peu "let a = 1 in a")

let tests =
  "Pure demand interpreter tests"
  >::: [
         "Numericals" >:: test_numerical;
         "Logicals" >:: test_logical;
         "Relationals" >:: test_relational;
         "Let" >:: test_let;
         "If" >:: test_if;
         "Function" >:: test_function;
         "Application" >:: test_basic_application;
         "Application (non-local lookups)" >:: test_involved_application;
         "Y Combinator" >:: test_ycomb;
         "Laziness" >:: test_laziness;
         "Record operations" >:: test_record;
         "Record rec" >:: test_record_rec;
         (* Uncomment the following to run custom tests *)
         (* "Custom" >:: test_custom; *)
       ]

let () =
  Arg.parse
    [
      ( "--no-cache",
        Arg.Unit (fun _ -> Utils.caching := false),
        "Turn off caching" );
      ( "--runtime",
        Arg.Unit (fun _ -> Utils.report_runtime := true),
        "Report runtime (processor time)" );
      ( "--debug",
        Arg.Unit (fun _ -> Utils.debug := true),
        "Print debug messages to stdout" );
    ]
    (fun _ -> ())
    "Pure demand interpreter tests";

  run_test_tt_main tests
