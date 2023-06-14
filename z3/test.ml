[@@@warning "-26"]

open Z3
open Convert

let solver = Solver.mk_solver_s ctx "HORN"

(* (declare-fun Inv (Int) Bool)
   (assert (Inv 0))
   (assert (forall ((x Int)) (=> (and (< x 5) (Inv x)) (Inv (+ x 1))))) *)

let _ =
  set_global_param "fp.engine" "spacer";
  set_global_param "fp.xform.inline_eager" "false";
  set_global_param "fp.xform.inline_linear" "false";
  (* let int_sort = Arithmetic.Integer.mk_sort ctx in
     let bool_sort = Boolean.mk_sort ctx in
     let inv = FuncDecl.mk_func_decl_s ctx "Inv" [ int_sort ] bool_sort in
     let a1 = Expr.mk_app ctx inv [ Arithmetic.Integer.mk_numeral_i ctx 0 ] in
     let a2 =
       let x_const = Expr.mk_fresh_const ctx "x" int_sort in
       Quantifier.expr_of_quantifier
         (Quantifier.mk_forall_const ctx [ x_const ]
            (Boolean.mk_implies ctx
               (Boolean.mk_and ctx
                  [
                    Arithmetic.mk_lt ctx x_const
                      (Arithmetic.Integer.mk_numeral_i ctx 5);
                    Expr.mk_app ctx inv [ x_const ];
                  ])
               (Expr.mk_app ctx inv
                  [
                    Arithmetic.mk_add ctx
                      [ x_const; Arithmetic.Integer.mk_numeral_i ctx 1 ];
                  ]))
            None [] [] None None)
     in
     Solver.add solver [ a1; a2 ]; *)
  (* Core.List.iter (Convert.test2 ()) ~f:(fun x -> print_endline @@ Expr.to_string x); *)
  let assns, negs = Convert.test7 () in
  Solver.add solver (List.tl negs @ CHCSet.elements assns);
  (* solver |> Solver.to_string |> Format.printf "Solver:\n%s"; *)
  match Solver.check solver [] with
  | SATISFIABLE -> (
      Solver.reset solver;
      Solver.add solver (CHCSet.elements assns @ [ List.hd negs ]);
      match Solver.check solver [] with
      | SATISFIABLE -> Format.printf "sat -> sat\n"
      | UNSATISFIABLE ->
          (* let model = solver |> Solver.get_model |> Option.get in *)
          (* model |> Model.to_string |> Format.printf "Model:\n%s\n\n"; *)
          solver |> Solver.to_string |> Format.printf "Solver:\n%s";
          let proof = Option.get @@ Solver.get_proof solver in
          Format.printf "sat -> unsat\n%s\n" (Expr.to_string proof)
      | UNKNOWN -> failwith "sat -> unknown"
      (* let e =
           Model.eval model
             (Expr.mk_app ctx inv [ Arithmetic.Integer.mk_numeral_i ctx 1 ])
             false
           |> Option.get
         in
         e |> Expr.to_string |> Format.printf "Inv: %s\n" *))
  | UNSATISFIABLE -> (
      match Solver.check solver [ Core.List.last_exn negs ] with
      | SATISFIABLE -> Format.printf "unsat -> sat\n"
      | UNSATISFIABLE -> Format.printf "unsat -> unsat\n"
      | UNKNOWN -> failwith "unsat -> unknown")
  | UNKNOWN ->
      Format.printf "unknown\n\n";
      solver |> Solver.to_string |> Format.printf "Solver:\n%s"
