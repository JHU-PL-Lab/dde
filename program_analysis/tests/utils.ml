open Interpreter
open Program_analysis
open Solver
open Test_cases

exception Unreachable

let pf = Format.printf

(** PBT *)

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

(** General *)

(*? can't use Debugutils.parse_analyze *)
let pau ?(verify = true) ?(test_num = 0) s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Lib.analyze ~verify ~test_num
  |> Format.asprintf "%a" Utils.pp_res

let pau' ?(verify = true) ?(test_num = 0) s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> Pa_reworked.Lib.analyze ~verify ~test_num
  |> Format.asprintf "%a" Pa_reworked.Utils.pp_res

let pau'' = Display_pa.Debugutils.pau
