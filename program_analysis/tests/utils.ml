open Interp
open Pa
open Solver
open Test_cases

exception Unreachable

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

let pau ?(verify = true) ?(test_num = 0)
    ?(test_name = Format.sprintf "Test %d" test_num) ?(time = true) s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> fun e ->
  let before = Sys.time () in
  let r = Lib.analyze e ~verify ~test_num in
  let after = Sys.time () in
  if time then (
    Format.printf "%s: %f\n" test_name (after -. before);
    flush_all ());
  r |> Format.asprintf "%a" Utils.pp_res

let pau' ?(verify = true) ?(test_num = 0)
    ?(test_name = Format.sprintf "Test %d" test_num) ?(time = true) s =
  s |> Core.Fn.flip ( ^ ) ";;" |> Lexing.from_string |> Parser.main Lexer.token
  |> fun e ->
  let before = Sys.time () in
  let r = Simple_pa.Lib.analyze e ~verify ~test_num in
  let after = Sys.time () in
  if time then (
    Format.printf "%s: %f\n" test_name (after -. before);
    flush_all ());
  r |> Core.Set.elements |> Format.asprintf "%a" Simple_pa.Utils.pp_res

let pau'' = Display_pa.Debugutils.pau
