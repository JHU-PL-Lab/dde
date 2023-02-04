(* open OUnit2
   open Utils

   let pa_basics _ =
     assert_equal
       (dde_eval_fb "(fun x -> fun y -> x) ((fun z -> z + 1) (1 + 2 + 3));;")
       (dde_parse "fun y -> 7")

   let pa_self_tests =
     [ "Laziness" >:: test_laziness; "Memoization" >:: test_memoization ]

   let pa_self = "Program analysis against self" >::: dde_self_tests *)
