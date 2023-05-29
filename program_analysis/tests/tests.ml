open OUnit2
open Church
open Utils

let test_basics _ =
  assert_equal "1" (pau "(fun x -> x) 1;;");
  assert_equal "(1 + 2)" (pau "(fun y -> 1 + y) 2;;")

let test_nonlocal_lookup _ =
  assert_equal "(1 + 2)" (pau "(fun x -> (fun y -> x + y) 2) 1;;");
  assert_equal "(1 + 2)" (pau "((fun x -> fun y -> x + y) 1) 2;;");
  assert_equal "((3 + 1) + 2)"
    (pau "(fun x -> (fun y -> (fun z -> x + y + z) 2) 1) 3;;")

(* stack stitching is also needed at Var Local *)
let test_local_stitching _ =
  assert_equal "((1 + 1) + (1 + 1))"
    (pau
       "let add = fun num -> fun n -> n + num in\n\
        let add1 = add 1 in\n\
        let add1' = fun n -> add1 n in\n\
        add1 1 + add1' 1;;");
  assert_equal "((0 + 1) + 2)"
    (pau
       "let add = fun f -> fun g -> fun x -> f g x in\n\
        let add1 = add (fun z -> fun n -> z n + 2) in\n\
        let add2 = add1 (fun y -> y + 1) in\n\
        add2 0;;")

let test_if _ =
  assert_equal "((n = 0) = false ⊩ (1 + (10 - 1)))"
    (pau "(fun id -> id 10) (fun n -> if n = 0 then 0 else 1 + (n - 1));;");
  assert_equal "(true = true ⊩ 1)" (pau "if true then 1 else 2;;");
  assert_equal "1"
    (pau "(fun x -> (if true then (fun y -> y) else (fun z -> z)) x) 1;;")

let test_currying _ =
  assert_equal "(2 + 1)"
    (pau "let add = fun num -> fun n -> n + num in let add1 = add 1 in add1 2;;");
  assert_equal "(2 + 1)"
    (pau
       "(fun add -> (fun add1 -> (fun add2 -> add1 2) (add 2)) (add 1)) (fun \
        num -> fun n -> n + num);;");
  assert_equal "(1 + 2)"
    (pau "let add = fun num -> fun n -> n + num in let add2 = add 2 in add2 1;;");
  assert_equal "((2 + 1) + (1 + 2))"
    (pau
       "let add = fun num -> fun n -> n + num in let add1 = add 1 in let add2 \
        = add 2 in add1 2 + add2 1;;");
  assert_equal "(((((1 + 1) + (1 + 2)) + (1 + 3)) + (1 + 4)) + (1 + 5))"
    (pau
       "let add = fun num -> fun n -> n + num in\n\
        let add1 = add 1 in\n\
        let add2 = add 2 in\n\
        let add3 = add 3 in\n\
        let add4 = add 4 in\n\
        let add5 = add 5 in\n\
        add1 1 + add2 1 + add3 1 + add4 1 + add5 1;;")

let test_recursion _ =
  assert_equal
    "((n = 0) = false ⊩ (1 + ((n = 0) = false ⊩ (1 + ((n = 0) = false ⊩ (1 + \
     (((n = 0) = false ⊩ (1 + stub)) | ((n = 0) = true ⊩ 0))))))))"
    (pau
       "let id = fun self -> fun n -> if n = 0 then 0 else 1 + self self (n - \
        1) in id id 10;;")

let test_pa =
  [
    "Basics" >:: test_basics;
    "Non-local variable lookup" >:: test_nonlocal_lookup;
    "Var local stack stitching" >:: test_local_stitching;
    "If" >:: test_if;
    "Currying" >:: test_currying;
    "Recursion" >:: test_recursion;
    "Church numerals" >::: test_church;
  ]

let tests = "Program analysis tests" >::: test_pa

let () =
  (* Pbt.run (); *)
  run_test_tt_main tests
