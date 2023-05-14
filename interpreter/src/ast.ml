open Base_quickcheck
open Sexplib.Std
open Core

exception Unreachable

type ident =
  | Ident of
      (string
      [@quickcheck.generator
        Generator.string_non_empty_of Generator.char_lowercase])
[@@coverage off] [@@deriving show { with_path = false }, quickcheck, sexp_of]

type expr =
  | Int of int [@quickcheck.weight 0.05]
  | Bool of bool [@quickcheck.weight 0.05]
  | Function of ident * expr * int [@quickcheck.weight 0.05]
  | Var of ident * int [@quickcheck.weight 0.2]
  | Appl of
      expr
      (*[@quickcheck.generator
        Generator.filter quickcheck_generator_expr ~f:(function
          | Function _ | Appl _ | If _ | Var _ -> true
          | _ -> false)]*)
      * expr
      * int [@quickcheck.weight 0.3]
  | Plus of expr * expr [@quickcheck.weight 0.05]
  | Minus of expr * expr [@quickcheck.weight 0.05]
  | Equal of expr * expr [@quickcheck.weight 0.05]
  | And of expr * expr [@quickcheck.weight 0.05]
  | Or of expr * expr [@quickcheck.weight 0.05]
  | Not of expr [@quickcheck.weight 0.05]
  | If of expr * expr * expr * int [@quickcheck.weight 0.05]
  | Let of ident * expr * expr * int [@quickcheck.do_not_generate]
[@@deriving show { with_path = false }, quickcheck, sexp_of]

type fbtype = TArrow of fbtype * fbtype | TVar of string
[@@coverage off] [@@deriving show { with_path = false }]

let myexpr = Hashtbl.create (module Int)
let myfun = Hashtbl.create (module Int)
let get_myexpr label = Hashtbl.find_exn myexpr label
let add_myexpr label e = Hashtbl.set myexpr ~key:label ~data:e
let get_myfun label = Hashtbl.find_exn myfun label

let add_myfun label outer =
  if Option.is_some outer then
    Hashtbl.set myfun ~key:label ~data:(Option.value_exn outer)

let rec build_myfun e outer =
  match e with
  | Int _ -> ()
  | Bool _ -> ()
  | Function (i, e', l) ->
      add_myfun l outer;
      build_myfun e' (Some e)
  | Var (_, l) -> add_myfun l outer
  | Appl (e1, e2, l) ->
      add_myfun l outer;
      build_myfun e1 outer;
      build_myfun e2 outer
  | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) | And (e1, e2) | Or (e1, e2)
    ->
      build_myfun e1 outer;
      build_myfun e2 outer
  | Not e -> build_myfun e outer
  | If (e1, e2, e3, l) ->
      add_myfun l outer;
      build_myfun e1 outer;
      build_myfun e2 outer;
      build_myfun e3 outer
  | Let (_, _, _, _) -> raise Unreachable [@coverage off]

let print_myexpr tbl =
  Hashtbl.to_alist tbl
  |> List.sort ~compare:(fun (k1, v1) (k2, v2) -> compare k1 k2)
  |> List.iter ~f:(fun (k, v) -> Format.printf "%d -> %s\n" k (show_expr v))
  [@@coverage off]

let print_myfun tbl =
  Hashtbl.iteri
    ~f:(fun ~key ~data -> Format.printf "%d -> %s\n" key (show_expr data))
    tbl
  [@@coverage off]

let next_label = ref 0

let get_next_label () =
  let l = !next_label in
  next_label := l + 1;
  l

let reset_label () = next_label := 0

let rec transform_let e =
  match e with
  | Int _ | Bool _ -> e
  | Function (ident, e, l) ->
      let e' = transform_let e in
      let f = Function (ident, e', l) in
      add_myexpr l f;
      f
  | Let (ident, e1, e2, let_l) ->
      let fun_l = get_next_label () in
      let e2' = transform_let e2 in
      let f = Function (ident, e2', fun_l) in
      add_myexpr fun_l f;
      let e1' = transform_let e1 in
      let appl = Appl (f, e1', let_l) in
      add_myexpr let_l appl;
      appl
  | Appl (e1, e2, l) ->
      let e1' = transform_let e1 in
      let e2' = transform_let e2 in
      let appl = Appl (e1', e2', l) in
      add_myexpr l appl;
      appl
  | _ -> e

let clean_up () =
  Core.Hashtbl.clear myexpr;
  Core.Hashtbl.clear myfun

let build_int i = Int i
let build_bool b = Bool b

let build_function ident e =
  let label = get_next_label () in
  let labeled_function = Function (ident, e, label) in
  add_myexpr label labeled_function;
  labeled_function

let build_appl e1 e2 =
  let label = get_next_label () in
  let labeled_appl = Appl (e1, e2, label) in
  add_myexpr label labeled_appl;
  labeled_appl

let build_var ident =
  let label = get_next_label () in
  let labeled_var = Var (ident, label) in
  add_myexpr label labeled_var;
  labeled_var

let build_plus e1 e2 = Plus (e1, e2)
let build_minus e1 e2 = Minus (e1, e2)
let build_equal e1 e2 = Equal (e1, e2)
let build_and e1 e2 = And (e1, e2)
let build_or e1 e2 = Or (e1, e2)
let build_not e = Not e

let build_if e1 e2 e3 =
  let label = get_next_label () in
  let labeled_if = If (e1, e2, e3, label) in
  add_myexpr label labeled_if;
  labeled_if

let build_let ident e1 e2 =
  let label = get_next_label () in
  let labeled_let = Let (ident, e1, e2, label) in
  add_myexpr label labeled_let;
  labeled_let
