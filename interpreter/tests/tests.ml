[@@@warning "-32"]

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
  assert_equal "8" (peu ~should_simplify:true (dde_fib 6));
  assert_equal "15"
    (peu ~should_simplify:true
       "let summate0 = fun self -> fun arg -> if arg = 0 then 0 else arg + \
        self self (arg - 1) in summate0 summate0 5")

let test_laziness _ =
  assert_equal "{ x = 1 + 1; y = 1 + 1 }"
    (peu "{ x = 1 + 1; y = (fun z -> z + 1) 1 }");
  assert_equal "1" (peu "{ x = 1 }.x");
  assert_equal "1" (peu "{ label = if true then 1 else 0 }.label");
  assert_equal "fun y -> 7"
    (peu ~should_simplify:true
       "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3))");
  assert_equal "fun y -> 1"
    (peu ~should_simplify:true "(fun x -> fun y -> x) (if true then 1 else 0)")

let test_memoization _ =
  (* assert_equal "" (peu ~should_simplify:true (Tests_subst.dde_fib 15)); *)
  assert_equal ""
    (peu ~should_simplify:false
       "let fib = (fun self -> fun n -> if n = 0 or n = 1 then n else self \
        self (n - 1) + self self (n - 2)) in fib fib 21")

let test_record _ =
  (* gives value at leftmost x *)
  assert_equal "1" (peu ~should_simplify:true "{ x = 1; y = 3; x = 2 }.x");
  assert_equal "{ counter = -98; cond = true }"
    (peu ~should_simplify:true
       "let data = { counter = 99; cond = false } in if data.cond then { \
        counter = data.counter + 1; cond = false } else { counter = 1 - \
        data.counter; cond = true }");
  assert_equal "1"
    (peu ~should_simplify:true
       "(fun r -> if green in r then r.green else if blue in r then r.blue \
        else r.red) ({ cyan = 10; blue = 1 })");
  assert_equal "2"
    (peu ~should_simplify:true "{ hd = 1; tl = { hd = 2; tl = {} } }.tl.hd")

let test_letassert _ =
  assert_equal "2" (peu ~should_simplify:true "letassert x = 1 + 1 in x = 2")

let list_incr =
  "let incr = fun self -> fun ls -> { hd = ls.hd + 1; tl = if hd in ls.tl then \
   self self (ls.tl) else {} } in incr incr"

let incr_cell =
  "let incr = fun self -> fun ls -> fun n -> if n = 0 then ls else self self \
   ({ hd = ls.hd + 1; tl = {} }) (n - 1) in incr incr"

let test_record_rec _ =
  assert_equal
    "{ hd = 2; tl = { hd = 3; tl = { hd = 4; tl = { hd = 5; tl = {} } } } }"
    (peu ~should_simplify:true
       (list_incr
      ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = {} } } \
         } })"));
  assert_equal "{ hd = 5; tl = {} }"
    (peu ~should_simplify:true (incr_cell ^ " ({ hd = 0; tl = {} }) 5"))

let test_misc _ =
  assert_equal ""
    (peu
       "let append = fun self -> fun x -> fun y ->\n\
       \  if not (hd in x) then y\n\
       \  else { hd = x.hd; tl = self self (x.tl) y }\n\
        in\n\n\
        let flatten = fun self -> fun x ->\n\
       \  if not (hd in x) then x\n\
       \  else if not (hd in x.hd) then self self (x.tl)\n\
       \  else if hd in (x.hd) then { hd = x.hd.hd; tl = self self (append \
        append (x.hd.tl) (x.tl)) }\n\
       \  else { hd = x.hd; tl = {} }\n\
        in\n\n\
        flatten flatten ({ hd = { hd = 1; tl = { hd = 2; tl = {} } }; tl = { \
        hd = 3; tl = { hd = 4; tl = { hd = 5; tl = {} } } } })")

let tests =
  "DDE against self"
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
         (* "Memoization" >:: test_memoization; *)
         (* "Record rec" >:: test_record_rec; *)
         (* "Laziness" >:: test_laziness; *)
         (* "Record operations" >:: test_record; *)
         (* "letassert" >:: test_letassert; *)
         (* "Misc." >:: test_misc; *)
       ]

let () =
  (* let out_file = Core.Out_channel.create "logs" in
     Logs.set_reporter
       (Logs_fmt.reporter ~dst:(Format.formatter_of_out_channel out_file) ());
     Logs.set_level (Some Logs.Debug); *)
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  (* if !bench then Bench.fib_bench (); *)
  run_test_tt_main tests
