open OUnit2
open Utils

let test_numerical _ =
  assert_equal (dde_eval_env "1;;") (fbenv_eval "1;;");
  assert_equal (dde_eval_env "-2;;") (fbenv_eval "-2;;");
  assert_equal (dde_eval_env "1 + 2;;") (fbenv_eval "1 + 2;;");
  assert_equal (dde_eval_env "1 - 2;;") (fbenv_eval "1 - 2;;")

let test_logical _ =
  assert_equal (dde_eval_env "true;;") (fbenv_eval "True;;");
  assert_equal (dde_eval_env "false;;") (fbenv_eval "False;;");
  assert_equal (dde_eval_env "not true;;") (fbenv_eval "Not True;;");
  assert_equal (dde_eval_env "false or true;;") (fbenv_eval "False Or True;;");
  assert_equal (dde_eval_env "true and false;;") (fbenv_eval "True And False;;")

let test_relational _ =
  assert_equal (dde_eval_env "1 = 1;;") (fbenv_eval "1 = 1;;");
  assert_equal (dde_eval_env "-1 = 2;;") (fbenv_eval "-1 = 2;;")

let test_let _ =
  assert_equal
    (dde_eval_env "let y = false in y;;")
    (fbenv_eval "Let y = False In y;;");
  assert_equal
    (dde_eval_env "let x = 5 in let y = 10 in x + y = 15;;")
    (fbenv_eval "Let x = 5 In Let y = 10 In x + y = 15;;")

let test_if _ =
  assert_equal
    (dde_eval_env "if false then 0 else 1;;")
    (fbenv_eval "If False Then 0 Else 1;;");
  assert_equal
    (dde_eval_env "let x = 1 in if x + 2 = 3 then x - 1 else x + 1;;")
    (fbenv_eval "Let x = 1 In If x + 2 = 3 Then x - 1 Else x + 1;;")

let test_function _ =
  assert_equal (dde_eval_env "fun x -> x;;") (fbenv_eval "Fun x -> x;;");
  assert_equal (dde_eval_env "fun x -> 1;;") (fbenv_eval "Fun x -> 1;;");
  assert_equal
    (dde_eval_env "fun x -> fun y -> fun z -> y;;")
    (fbenv_eval "Fun x -> Fun y -> Fun z -> y;;")

let test_basic_application _ =
  assert_equal (dde_eval_env "(fun x -> x) 1;;") (fbenv_eval "(Fun x -> x) 1;;");
  assert_equal
    (dde_eval_env "(fun x -> 1) (-2);;")
    (fbenv_eval "(Fun x -> 1) (-2);;");
  assert_equal
    (dde_eval_env "((fun x -> fun y -> y) 1) 2;;")
    (fbenv_eval "((Fun x -> Fun y -> y) 1) 2;;")

let test_involved_application _ =
  assert_equal
    (dde_eval_env "((fun x -> fun y -> x) 1) 2;;")
    (fbenv_eval "((Fun x -> Fun y -> x) 1) 2;;");
  assert_equal
    (dde_eval_env "((fun x -> fun y -> y x) 1) (fun x -> x + 10);;")
    (fbenv_eval "((Fun x -> Fun y -> y x) 1) (Fun x -> x + 10);;");
  assert_equal
    (dde_eval_env "(fun x -> (fun y -> (fun z -> z + 1) y) (x + 2)) 6;;")
    (fbenv_eval "(Fun x -> (Fun y -> (Fun z -> z + 1) y) (x + 2)) 6;;");
  (* call-by-name semantics *)
  assert_unequal
    (dde_eval_env "(fun x -> fun y -> x) (1 + 2);;")
    (fbenv_eval "(Fun x -> Fun y -> x) (1 + 2);;")

let dde_ycomb =
  "(fun code -> let repl = fun self -> fun x -> code (self self) x in repl \
   repl)"

let dde_fib x =
  Format.asprintf
    "let fib = fun self -> fun x -> if x = 0 then 0 else x + self (x - 1) in \
     %s fib %d;;"
    dde_ycomb x

let fb_ycomb =
  "(Fun code -> Let repl = Fun self -> Fun x -> code (self self) x In repl \
   repl)"

let fb_fib x =
  Format.asprintf
    "Let fib = Fun self -> Fun x -> If x = 0 Then 0 Else x + self (x - 1) In \
     %s fib %d;;"
    fb_ycomb x

let test_ycomb _ =
  assert_equal
    (dde_eval_env
       "let summate0 = fun self -> fun arg -> if arg = 0 then 0 else arg + \
        self self (arg - 1) in summate0 summate0 5;;")
    (fbenv_eval
       "Let summate0 = Fun self -> Fun arg -> If arg = 0 Then 0 Else arg + \
        self self (arg - 1) In summate0 summate0 5;;");
  assert_equal (dde_eval_env @@ dde_fib 5) (fbenv_eval @@ fb_fib 5)

let dde_env_tests =
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

(* TODO: test with church numerals *)
let dde_env = "DDE against environment" >::: dde_env_tests
