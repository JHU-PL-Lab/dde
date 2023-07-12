open Interpreter
open Program_analysis

module IdentSet = Set.Make (struct
  type t = Ast.ident

  let compare ident1 ident2 =
    match (ident1, ident2) with
    | Ast.Ident id1, Ast.Ident id2 -> compare id1 id2
end)

let label = ref (-1)

let fresh_label () =
  label := !label + 1;
  !label

let reset_label () = label := -1
let ( |>> ) v f = Option.map f v
let ( |>-> ) v f = Option.bind v f

let pau s =
  s |> Debugutils.parse_analyze |> fun (r, _) ->
  Format.asprintf "%a" Utils.pp_res r

let pau' s = s |> Debugutils.parse_analyze |> snd

let verify_result chcs assns =
  let solver = Solver.solver in
  Z3.Solver.add solver chcs;
  match Z3.Solver.check solver assns with
  | SATISFIABLE ->
      Format.printf "sat\n\n";
      let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
      model |> Z3.Model.to_string |> Format.printf "Model:\n%s\n\n";
      solver |> Z3.Solver.to_string |> Format.printf "Solver:\n%s";
      true
  | UNSATISFIABLE ->
      Format.printf "unsat";
      false
  | UNKNOWN ->
      Format.printf "unknown";
      false
