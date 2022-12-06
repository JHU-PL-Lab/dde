exception Unreachable

type ident = Ident of string
[@@coverage off] [@@deriving show { with_path = false }]

type expr =
  | Int of int
  | Var of ident
  | Bool of bool
  | Function of ident * lexpr
  | Appl of lexpr * lexpr
  | Plus of lexpr * lexpr
  | Minus of lexpr * lexpr
  | Equal of lexpr * lexpr
  | And of lexpr * lexpr
  | Or of lexpr * lexpr
  | Not of lexpr
  | If of lexpr * lexpr * lexpr
  | Let of ident * lexpr * lexpr

and lexpr = expr * int [@@deriving show { with_path = false }]

(* type expr =
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
   [@@coverage off] [@@deriving show { with_path = false }] *)

type fbtype = TArrow of fbtype * fbtype | TVar of string
[@@coverage off] [@@deriving show { with_path = false }]

let my_expr : (int, lexpr) Hashtbl.t = Hashtbl.create 10000
let my_fun = Hashtbl.create 10000
let get_expr label = Hashtbl.find my_expr label
let add_expr label e = Hashtbl.replace my_expr label e
let get_outer_scope label = Hashtbl.find my_fun label

let add_outer_scope label outer =
  if Option.is_some outer then Hashtbl.replace my_fun label @@ Option.get outer

let rec fill_my_fun e outer =
  match e with
  | Int _, label | Bool _, label | Var _, label -> add_outer_scope label outer
  | Function (_, e'), label ->
      add_outer_scope label outer;
      fill_my_fun e' (Some e)
  | Appl (e1, e2), label ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | Plus (e1, e2), label
  | Minus (e1, e2), label
  | Equal (e1, e2), label
  | And (e1, e2), label
  | Or (e1, e2), label ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer
  | Not e, label ->
      add_outer_scope label outer;
      fill_my_fun e outer
  | If (e1, e2, e3), label ->
      add_outer_scope label outer;
      fill_my_fun e1 outer;
      fill_my_fun e2 outer;
      fill_my_fun e3 outer
  | Let (_, _, _), _ -> raise Unreachable [@coverage off]

let print_my_expr tbl =
  Hashtbl.iter (fun x y -> Printf.printf "%d -> %s\n" x (show_lexpr y)) tbl
  [@@coverage off]

let print_my_fun tbl =
  Hashtbl.iter (fun x y -> Printf.printf "%d -> %s\n" x (show_lexpr y)) tbl
  [@@coverage off]

let next_label = ref 0
let make_lexpr e label : lexpr = (e, label)

let get_next_label () =
  let l = !next_label in
  next_label := l + 1;
  l

let build_labeled_int i =
  let label = get_next_label () in
  let labeled_int = make_lexpr (Int i) label in
  add_expr label labeled_int;
  labeled_int

let build_labeled_bool b =
  let label = get_next_label () in
  let labeled_bool = make_lexpr (Bool b) label in
  add_expr label labeled_bool;
  labeled_bool

let build_labeled_function ident e =
  let label = get_next_label () in
  let labeled_function = make_lexpr (Function (ident, e)) label in
  add_expr label labeled_function;
  labeled_function

let build_labeled_appl e1 e2 =
  let label = get_next_label () in
  let labeled_appl = make_lexpr (Appl (e1, e2)) label in
  add_expr label labeled_appl;
  labeled_appl

let build_labeled_var ident =
  let label = get_next_label () in
  let labeled_var = make_lexpr (Var ident) label in
  add_expr label labeled_var;
  labeled_var

let build_labeled_plus e1 e2 =
  let label = get_next_label () in
  let labeled_plus = make_lexpr (Plus (e1, e2)) label in
  add_expr label labeled_plus;
  labeled_plus

let build_labeled_minus e1 e2 =
  let label = get_next_label () in
  let labeled_minus = make_lexpr (Minus (e1, e2)) label in
  add_expr label labeled_minus;
  labeled_minus

let build_labeled_equal e1 e2 =
  let label = get_next_label () in
  let labeled_equal = make_lexpr (Equal (e1, e2)) label in
  add_expr label labeled_equal;
  labeled_equal

let build_labeled_and e1 e2 =
  let label = get_next_label () in
  let labeled_and = make_lexpr (And (e1, e2)) label in
  add_expr label labeled_and;
  labeled_and

let build_labeled_or e1 e2 =
  let label = get_next_label () in
  let labeled_or = make_lexpr (Or (e1, e2)) label in
  add_expr label labeled_or;
  labeled_or

let build_labeled_not e =
  let label = get_next_label () in
  let labeled_not = make_lexpr (Not e) label in
  add_expr label labeled_not;
  labeled_not

let build_labeled_if e1 e2 e3 =
  let label = get_next_label () in
  let labeled_if = make_lexpr (If (e1, e2, e3)) label in
  add_expr label labeled_if;
  labeled_if

let build_labeled_let ident e1 e2 =
  let label = get_next_label () in
  let labeled_let = make_lexpr (Let (ident, e1, e2)) label in
  add_expr label labeled_let;
  labeled_let
