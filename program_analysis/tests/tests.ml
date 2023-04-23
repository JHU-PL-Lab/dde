open OUnit2
open Utils

let test_basics _ =
  assert_equal "| | 1" (pau "(fun x -> x) 1;;");
  assert_equal "| (1 + | 2)" (pau "(fun y -> 1 + y) 2;;")

let test_nonlocal _ =
  assert_equal "| | (| | 1 + | 2)" (pau "(fun x -> (fun y -> x + y) 2) 1;;");
  assert_equal "| (| | 1 + | 2)" (pau "((fun x -> fun y -> x + y) 1) 2;;");
  assert_equal "| | (| | 1 + | 2)"
    (pau "(fun x -> (fun y -> (fun z -> x + y + z) 2) 1) 3;;")

let test_if _ =
  assert_equal "| | (0 | (1 + (| 10 - 1)))"
    (pau "(fun id -> id 10) (fun n -> if n = 0 then 0 else 1 + (n - 1));;")

let _test_curried_funs _ =
  assert_equal "TODO"
    (pau "let add = fun num -> fun n -> n + num in let add1 = add 1 in add1 2");
  assert_equal "TODO"
    (pau
       "(fun add -> (fun add1 -> (fun add2 -> add1 2) (add 2)) (add 1)) (fun \
        num -> fun n -> n + num)");
  assert_equal "TODO"
    (pau "let add = fun num -> fun n -> n + num in let add2 = add 2 in add2 1");
  assert_equal "TODO"
    (pau
       "let add = fun num -> fun n -> n + num in let add1 = add 1 in let add2 \
        = add 2 in add1 2 + add2 1")

let _test_recursion _ =
  assert_equal "TODO"
    (pau
       "let id = fun self -> fun n -> if n = 0 then 0 else 1 + self self (n - \
        1) in id id 10;;")

let pa_tests =
  [
    "Basics" >:: test_basics;
    "Non-local variable lookup" >:: test_nonlocal;
    "If" >:: test_if;
  ]

let tests = "Program analysis tests" >::: pa_tests

let () =
  (* Pbt.run (); *)
  run_test_tt_main tests
