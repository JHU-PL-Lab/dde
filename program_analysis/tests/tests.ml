open OUnit2
open Church
open Utils
open Core

let gen_test ls =
  List.iter ls ~f:(fun f ->
      let expected, actual = f () in
      assert_equal expected actual)

let basic =
  [
    (fun _ -> ("1", pau "(fun x -> x) 1;;"));
    (fun _ -> ("(1 + 2)", pau "(fun y -> 1 + y) 2;;"));
  ]

let test_basic _ = gen_test basic

let nonlocal_lookup =
  [
    (fun _ -> ("(1 + 2)", pau "(fun x -> (fun y -> x + y) 2) 1;;"));
    (fun _ -> ("(1 + 2)", pau "((fun x -> fun y -> x + y) 1) 2;;"));
    (fun _ ->
      ("((3 + 1) + 2)", pau "(fun x -> (fun y -> (fun z -> x + y + z) 2) 1) 3;;"));
  ]

let test_nonlocal_lookup _ = gen_test nonlocal_lookup

let local_stitching =
  [
    (fun _ ->
      ( "((1 + 1) + (1 + 1))",
        pau
          "let add = (fun num -> fun n -> n + num) in\n\
           let add1 = add 1 in\n\
           let add1' = (fun n -> add1 n) in\n\
           add1 1 + add1' 1;;" ));
    (fun _ ->
      ( "((0 + 1) + 2)",
        pau
          "let add = (fun f -> fun g -> fun x -> f g x) in\n\
           let add1 = add (fun z -> fun n -> z n + 2) in\n\
           let add2 = add1 (fun y -> y + 1) in\n\
           add2 0;;" ));
  ]

(* stack stitching is also needed at Var Local *)
let test_local_stitching _ = gen_test local_stitching

let conidtional =
  [
    (fun _ ->
      ( "((10 = 0) = false ⊩ (1 + (10 - 1)))",
        pau "(fun id -> id 10) (fun n -> if n = 0 then 0 else 1 + (n - 1));;" ));
    (fun _ -> ("(true = true ⊩ 1)", pau "if true then 1 else 2;;"));
    (fun _ ->
      ("1", pau "(fun x -> (if true then (fun y -> y) else (fun z -> z)) x) 1;;"));
  ]

let test_conditional _ = gen_test conidtional

let currying =
  [
    (fun _ ->
      ( "(2 + 1)",
        pau
          "let add = (fun num -> fun n -> n + num) in let add1 = add 1 in add1 \
           2;;" ));
    (fun _ ->
      ( "(2 + 1)",
        pau
          "(fun add -> (fun add1 -> (fun add2 -> add1 2) (add 2)) (add 1)) \
           (fun num -> fun n -> n + num);;" ));
    (fun _ ->
      ( "(1 + 2)",
        pau
          "let add = (fun num -> fun n -> n + num) in let add2 = add 2 in add2 \
           1;;" ));
    (fun _ ->
      ( "((2 + 1) + (1 + 2))",
        pau
          "let add = (fun num -> fun n -> n + num) in let add1 = add 1 in let \
           add2 = add 2 in add1 2 + add2 1;;" ));
    (fun _ ->
      ( "(((((1 + 1) + (1 + 2)) + (1 + 3)) + (1 + 4)) + (1 + 5))",
        pau
          "let add = (fun num -> fun n -> n + num) in\n\
           let add1 = add 1 in\n\
           let add2 = add 2 in\n\
           let add3 = add 3 in\n\
           let add4 = add 4 in\n\
           let add5 = add 5 in\n\
           add1 1 + add2 1 + add3 1 + add4 1 + add5 1;;" ));
  ]

let test_currying _ = gen_test currying

let recursion =
  [
    (fun _ ->
      (* TODO: make more readable *)
      ( "((10 = 0) = false ⊩ (1 + (((10 - 1) = 0) = false ⊩ (1 + ((((10 - 1) - \
         1) = 0) = false ⊩ (1 + ((((((10 - 1) - 1) | ((((10 - 1) - 1) | (stub \
         - 1)) - 1)) = 0) = false ⊩ (1 + stub)) | (((((10 - 1) - 1) | ((((10 - \
         1) - 1) | (stub - 1)) - 1)) = 0) = true ⊩ 0))))))))",
        pau
          "let id = fun self -> fun n -> if n = 0 then 0 else 1 + self self (n \
           - 1) in id id 10;;" ));
  ]

let test_recursion _ = gen_test recursion

let all_tests =
  basic @ nonlocal_lookup @ local_stitching @ conidtional @ currying @ recursion

let test_pa =
  [
    "Basics" >:: test_basic;
    "Non-local variable lookup" >:: test_nonlocal_lookup;
    "Var local stack stitching" >:: test_local_stitching;
    "If" >:: test_conditional;
    "Currying" >:: test_currying;
    "Recursion" >:: test_recursion;
    "Church numerals" >::: test_church;
  ]

let tests = "Program analysis tests" >::: test_pa

let _ =
  (* Pbt.run _; *)
  let bench = ref false in
  Arg.parse [ ("--bench", Arg.Set bench, "run benchmarks") ] (fun _ -> ()) "";
  if !bench then Bench.run all_tests;
  run_test_tt_main tests
