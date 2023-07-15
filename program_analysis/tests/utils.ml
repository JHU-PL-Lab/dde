open Interpreter
open Program_analysis
open Solver
open Test_cases

exception Unreachable

let pf = Format.printf

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

(* TODO: can't use Debugutils.parse_analyze *)
let pau s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Lib.analyze ~debug:false
  |> Format.asprintf "%a" Utils.pp_res

let pau' ?(entry = "P0") s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Lib.analyze ~debug:false
  |> fun r ->
  (* pf "result: %a\n" Grammar.pp_res r; *)
  Solver.chcs_of_res r;
  let chcs = Solver.list_of_chcs () in

  let entry = Option.get !Solver.entry_decl in

  (* Format.printf "CHCs:\n";
     List.iter ~f:(fun chc -> Format.printf "%s\n" (Z3.Expr.to_string chc)) chcs; *)
  Solver.reset ();
  (chcs, entry)

let verify_result { prog; verif } =
  (* pf "\nTest: %s\n" prog; *)
  let solver = Solver.solver in
  let chcs, p = pau' prog in
  Z3.Solver.add solver (verif p :: chcs);

  match Z3.Solver.check solver [] with
  | SATISFIABLE ->
      (* pf "\nsat\n\n";
         let model = solver |> Z3.Solver.get_model |> Core.Option.value_exn in
         model |> Z3.Model.to_string |> pf "Model:\n%s\n\n";
         solver |> Z3.Solver.to_string |> pf "Solver:\n%s"; *)
      true
  | UNSATISFIABLE ->
      pf "unsat\n";
      false
  | UNKNOWN ->
      pf "unknown\n";
      false
