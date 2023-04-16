open Base_quickcheck
open Sexplib.Std

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

let my_expr = Core.Hashtbl.create (module Core.Int)
let my_fun = Hashtbl.create 10000
let get_expr label = Core.Hashtbl.find_exn my_expr label
let add_expr label e = Core.Hashtbl.set my_expr ~key:label ~data:e
let get_outer_scope label = Hashtbl.find my_fun label

let add_outer_scope label outer =
  if Option.is_some outer then Hashtbl.replace my_fun label @@ Option.get outer

let rec fill_my_fun e outer =
  match e with
  | Int _ -> ()
  | Bool _ -> ()
  | Function (i, e', l) ->
      add_outer_scope l outer;
      fill_my_fun e' (Some e)
  | Var (_, l) -> add_outer_scope l outer
  | Appl (e1, e2, l) ->
      add_outer_scope l outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) | And (e1, e2) | Or (e1, e2)
    ->
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | Not e -> fill_my_fun e outer
  | If (e1, e2, e3, l) ->
      add_outer_scope l outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer;
      fill_my_fun e3 outer
  | Let (_, _, _, _) -> raise Unreachable [@coverage off]

let print_my_expr tbl =
  let sorted =
    Core.Hashtbl.to_alist tbl
    |> List.sort (fun (k1, v1) (k2, v2) -> Int.compare k1 k2)
  in
  List.iter (fun (k, v) -> Format.printf "%d -> %s\n" k (show_expr v)) sorted
  [@@coverage off]

let print_my_fun tbl =
  Hashtbl.iter (fun x y -> Format.printf "%d -> %s\n" x (show_expr y)) tbl
  [@@coverage off]

let next_label = ref 0

let get_next_label () =
  let l = !next_label in
  next_label := l + 1;
  l

let rec transform_let e =
  match e with
  | Int _ | Bool _ -> e
  | Function (ident, e, l) ->
      let e' = transform_let e in
      let f = Function (ident, e', l) in
      add_expr l f;
      f
  | Let (ident, e1, e2, let_l) ->
      let fun_l = get_next_label () in
      let e2' = transform_let e2 in
      let f = Function (ident, e2', fun_l) in
      add_expr fun_l f;
      let e1' = transform_let e1 in
      let appl = Appl (f, e1', let_l) in
      add_expr let_l appl;
      appl
  | Appl (e1, e2, l) ->
      let e1' = transform_let e1 in
      let e2' = transform_let e2 in
      let appl = Appl (e1', e2', l) in
      add_expr l appl;
      appl
  | _ -> e

let build_labeled_int i = Int i

let build_labeled_bool b =
  let label = get_next_label () in
  let labeled_bool = Bool b in
  add_expr label labeled_bool;
  labeled_bool

let build_labeled_function ident e =
  let label = get_next_label () in
  let labeled_function = Function (ident, e, label) in
  add_expr label labeled_function;
  labeled_function

let build_labeled_appl e1 e2 =
  let label = get_next_label () in
  let labeled_appl = Appl (e1, e2, label) in
  add_expr label labeled_appl;
  labeled_appl

let build_labeled_var ident =
  let label = get_next_label () in
  let labeled_var = Var (ident, label) in
  add_expr label labeled_var;
  labeled_var

let build_labeled_plus e1 e2 = Plus (e1, e2)
let build_labeled_minus e1 e2 = Minus (e1, e2)
let build_labeled_equal e1 e2 = Equal (e1, e2)
let build_labeled_and e1 e2 = And (e1, e2)
let build_labeled_or e1 e2 = Or (e1, e2)
let build_labeled_not e = Not e

let build_labeled_if e1 e2 e3 =
  let label = get_next_label () in
  let labeled_if = If (e1, e2, e3, label) in
  add_expr label labeled_if;
  labeled_if

let build_labeled_let ident e1 e2 =
  let label = get_next_label () in
  let labeled_let = Let (ident, e1, e2, label) in
  add_expr label labeled_let;
  labeled_let
