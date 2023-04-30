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

let au e =
  e
  |> Lib.analyze ~is_debug_mode:false
  |> Format.asprintf "%a" Debugutils.pp_result_value

let pau s = Lexing.from_string s |> Parser.main Lexer.token |> au
