[@@@coverage off]

type ident = Ident of string [@@deriving show { with_path = false }]

(* type expr =
     | Label of labelexpr
     | Int of int
     | Var of ident * int
     | Bool of bool
     | Function of ident * expr
     | Appl of expr * expr
     | Plus of expr * expr
     | Minus of expr * expr
     | Equal of expr * expr
     | And of expr * expr
     | Or of expr * expr
     | Not of expr
     | If of expr * expr * expr
     | Let of ident * expr * expr
   [@@deriving show { with_path = false }]

   and labelexpr = expr * int *)

type expr =
  | Int of int * int
  | Var of ident * int
  | Bool of bool * int
  | Function of ident * expr * int
  | Appl of expr * expr * int
  | Plus of expr * expr * int
  | Minus of expr * expr * int
  | Equal of expr * expr * int
  | And of expr * expr * int
  | Or of expr * expr * int
  | Not of expr * int
  | If of expr * expr * expr * int
  | Let of ident * expr * expr * int
[@@deriving show { with_path = false }]

type fbtype = TArrow of fbtype * fbtype | TVar of string
[@@deriving show { with_path = false }]

let my_expr = Hashtbl.create 10000
let my_fun = Hashtbl.create 10000
let get_expr label = Hashtbl.find my_expr label
let add_expr label e = Hashtbl.replace my_expr label e
let get_outer_scope label = Hashtbl.find my_fun label

let add_outer_scope label outer =
  if Option.is_some outer then Hashtbl.replace my_fun label @@ Option.get outer

let rec fill_my_fun e outer =
  match e with
  | Int (_, label) -> add_outer_scope label outer
  | Function (_, e, label) ->
      add_outer_scope label outer;
      fill_my_fun e (Some label)
  | Bool (_, label) -> add_outer_scope label outer
  | Appl (e1, e2, label) ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | Var (_, label) -> add_outer_scope label outer
  | Plus (e1, e2, label) | Minus (e1, e2, label) | Equal (e1, e2, label) ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | And (e1, e2, label) | Or (e1, e2, label) ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | Not (e, label) ->
      add_outer_scope label outer;
      fill_my_fun e outer
  | If (e1, e2, e3, label) ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer;
      fill_my_fun e3 outer
  | Let (_, _, _, _) -> failwith "unreachable"

let print_my_expr tbl =
  Hashtbl.iter (fun x y -> Printf.printf "%d -> %s\n" x (show_expr y)) tbl

let print_my_fun tbl =
  Hashtbl.iter (fun x y -> Printf.printf "%d -> %d\n" x y) tbl

let next_label = ref 0

let get_next_label () =
  let l = !next_label in
  next_label := l + 1;
  l

let build_labeled_int i =
  let label = get_next_label () in
  let labeled_int = Int (i, label) in
  add_expr label labeled_int;
  labeled_int

let build_labeled_bool b =
  let label = get_next_label () in
  let labeled_bool = Bool (b, label) in
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

let build_labeled_plus e1 e2 =
  let label = get_next_label () in
  let labeled_plus = Plus (e1, e2, label) in
  add_expr label labeled_plus;
  labeled_plus

let build_labeled_minus e1 e2 =
  let label = get_next_label () in
  let labeled_minus = Minus (e1, e2, label) in
  add_expr label labeled_minus;
  labeled_minus

let build_labeled_equal e1 e2 =
  let label = get_next_label () in
  let labeled_equal = Equal (e1, e2, label) in
  add_expr label labeled_equal;
  labeled_equal

let build_labeled_and e1 e2 =
  let label = get_next_label () in
  let labeled_and = And (e1, e2, label) in
  add_expr label labeled_and;
  labeled_and

let build_labeled_or e1 e2 =
  let label = get_next_label () in
  let labeled_or = Or (e1, e2, label) in
  add_expr label labeled_or;
  labeled_or

let build_labeled_not e =
  let label = get_next_label () in
  let labeled_not = Not (e, label) in
  add_expr label labeled_not;
  labeled_not

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
