open OUnit2
open Utils

let test_numerical _ =
  assert_equal (dde_eval "1;;") (fb_eval "1;;");
  assert_equal (dde_eval "-2;;") (fb_eval "-2;;");
  assert_equal (dde_eval "1 + 2;;") (fb_eval "1 + 2;;");
  assert_equal (dde_eval "1 - 2;;") (fb_eval "1 - 2;;")

let test_logical _ =
  assert_equal (dde_eval "true;;") (fb_eval "True;;");
  assert_equal (dde_eval "false;;") (fb_eval "False;;");
  assert_equal (dde_eval "not true;;") (fb_eval "Not True;;");
  assert_equal (dde_eval "false or true;;") (fb_eval "False Or True;;");
  assert_equal (dde_eval "true and false;;") (fb_eval "True And False;;")

let test_relational _ =
  assert_equal (dde_eval "1 = 1;;") (fb_eval "1 = 1;;");
  assert_equal (dde_eval "-1 = 2;;") (fb_eval "-1 = 2;;")

let test_let _ =
  assert_equal
    (dde_eval "let y = false in y;;")
    (fb_eval "Let y = False In y;;");
  assert_equal
    (dde_eval "let x = 5 in let y = 10 in x + y = 15;;")
    (fb_eval "Let x = 5 In Let y = 10 In x + y = 15;;")

let test_if _ =
  assert_equal
    (dde_eval "if false then 0 else 1;;")
    (fb_eval "If False Then 0 Else 1;;");
  assert_equal
    (dde_eval "let x = 1 in if x + 2 = 3 then x - 1 else x + 1;;")
    (fb_eval "Let x = 1 In If x + 2 = 3 Then x - 1 Else x + 1;;")

let test_function _ =
  assert_equal (dde_eval "fun x -> x;;") (fb_eval "Fun x -> x;;");
  assert_equal (dde_eval "fun x -> 1;;") (fb_eval "Fun x -> 1;;");
  assert_equal
    (dde_eval "fun x -> fun y -> fun z -> y;;")
    (fb_eval "Fun x -> Fun y -> Fun z -> y;;")

let test_basic_application _ =
  assert_equal (dde_eval "(fun x -> x) 1;;") (fb_eval "(Fun x -> x) 1;;");
  assert_equal (dde_eval "(fun x -> 1) (-2);;") (fb_eval "(Fun x -> 1) (-2);;");
  assert_equal
    (dde_eval "((fun x -> fun y -> y) 1) 2;;")
    (fb_eval "((Fun x -> Fun y -> y) 1) 2;;")

let test_involved_application _ =
  assert_equal
    (dde_eval "((fun x -> fun y -> x) 1) 2;;")
    (fb_eval "((Fun x -> Fun y -> x) 1) 2;;");
  assert_equal
    (dde_eval "((fun x -> fun y -> y x) 1) (fun x -> x + 10);;")
    (fb_eval "((Fun x -> Fun y -> y x) 1) (Fun x -> x + 10);;");
  assert_equal
    (dde_eval "(fun x -> (fun y -> (fun z -> z + 1) y) (x + 2)) 6;;")
    (fb_eval "(Fun x -> (Fun y -> (Fun z -> z + 1) y) (x + 2)) 6;;");
  (* call-by-name semantics *)
  assert_unequal
    (dde_eval "(fun x -> fun y -> x) (1 + 2);;")
    (fb_eval "(Fun x -> Fun y -> x) (1 + 2);;")

let test_ycomb _ =
  assert_equal
    (dde_eval
       "let summate0 = fun self -> fun arg -> if arg = 0 then 0 else arg + \
        self self (arg - 1) in summate0 summate0 5;;")
    (fb_eval
       "Let summate0 = Fun self -> Fun arg -> If arg = 0 Then 0 Else arg + \
        self self (arg - 1) In summate0 summate0 5;;")

let dde_subst_tests =
  [
    "Numericals" >:: test_numerical;
    "Logicals" >:: test_logical;
    "Relationals" >:: test_relational;
    "Let" >:: test_let;
    "If" >:: test_if;
    "Function" >:: test_function;
    "Application" >:: test_basic_application;
    "Application (non-local lookups)" >:: test_involved_application;
    "Y Combinator" >:: test_ycomb;
  ]

(* TODO: test DDE against itself *)
let dde_subst = "DDE against substitution" >::: dde_subst_tests
let () = run_test_tt_main dde_subst
