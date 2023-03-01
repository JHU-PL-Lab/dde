open Core
open Program_analysis.Lib
open Test_utils

let expr_gen = Ddeast.quickcheck_generator_expr
(* let expr = Quickcheck.random_value ~seed:`Nondeterministic expr_gen
   let () = Format.printf "%a" Ddeast.pp_expr expr *)

(* let res = Base_quickcheck.Generator.generate res_gen ~size:10 ~:random:(Random.State.make_self_init ()) *)
let run () =
  Quickcheck.test ~sexp_of:Ddeast.sexp_of_expr expr_gen ~trials:5 ~f:(fun e ->
      e |> au |> ignore)

(*
   TODOs:
   - check number of |'s in output involving appls and lookups
   - check exception thrown
   - generated node labels are messed up
   - what does `size` mean for generating expr's
   - update with correct ids and use random existing vars in proogram
   - resolve programs with runtime type errors - smaller programs (~15 nodes)
   - papers on generating random programs
   - evaluate generated program and see if it falls in the range of the analysis
   - unevaluation (reverse evaluation, random test construction, random program synthesis) - reversing small-step semantics
*)