open Base_quickcheck
open Sexplib.Std
open Core

exception Unreachable

type ident =
  | Ident of
      (string
      [@quickcheck.generator
        Generator.string_non_empty_of Generator.char_lowercase])
[@@coverage off]
[@@deriving show { with_path = false }, quickcheck, compare, sexp, hash]

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
  | Ge of expr * expr [@quickcheck.weight 0.05]
  | Gt of expr * expr [@quickcheck.weight 0.05]
  | Le of expr * expr [@quickcheck.weight 0.05]
  | Lt of expr * expr [@quickcheck.weight 0.05]
  | Not of expr [@quickcheck.weight 0.05]
  | If of expr * expr * expr * int [@quickcheck.weight 0.05]
  | Let of ident * expr * expr * int [@quickcheck.do_not_generate]
  | LetAssert of ident * expr * expr [@quickcheck.do_not_generate]
  | Record of (ident * expr) list [@quickcheck.do_not_generate]
  | Projection of expr * ident [@quickcheck.do_not_generate]
  | Inspection of ident * expr [@quickcheck.do_not_generate]
[@@deriving show { with_path = false }, quickcheck, compare, sexp, hash]

type sigma = int list
[@@deriving show { with_path = false }, compare, sexp, hash]

type op_result_value =
  | PlusOp of result_value * result_value
  | MinusOp of result_value * result_value
  | EqualOp of result_value * result_value
  | AndOp of result_value * result_value
  | OrOp of result_value * result_value
  | GeOp of result_value * result_value
  | GtOp of result_value * result_value
  | LeOp of result_value * result_value
  | LtOp of result_value * result_value
  | NotOp of result_value

and result_value =
  | IntResult of int
  | BoolResult of bool
  | FunResult of { f : expr; l : int; sigma : int list }
  | OpResult of op_result_value
  | RecordResult of (ident * result_value) list
  | ProjectionResult of result_value * ident
  | InspectionResult of ident * result_value

type op_result_value_fv =
  | PlusOpFv of result_value_fv
  | MinusOpFv of result_value_fv
  | EqOpFv of result_value_fv
  | AndOpFv of result_value_fv * result_value_fv
  | OrOpFv of result_value_fv * result_value_fv
  | GeOpFv of result_value_fv
  | GtOpFv of result_value_fv
  | LeOpFv of result_value_fv
  | LtOpFv of result_value_fv
  | NotOpFv

(** result values that may contain free variables *)
and result_value_fv =
  | IntResultFv of int
  | BoolResultFv of bool
  | VarResultFv
  | OpResultFv of op_result_value_fv
  | FunResultFv
  | RecordResultFv
  | ProjectionResultFv
  | InspectionResultFv
[@@deriving hash, sexp, compare, show { with_path = false }]

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

let clean_up () =
  Hashtbl.clear myexpr;
  Hashtbl.clear myfun

let rec build_myfun e outer =
  match e with
  | Int _ -> ()
  | Bool _ -> ()
  | Function (_, e', l) ->
      add_myfun l outer;
      build_myfun e' (Some e)
  | Var (_, l) -> add_myfun l outer
  | Appl (e1, e2, l) ->
      add_myfun l outer;
      build_myfun e1 outer;
      build_myfun e2 outer
  | Plus (e1, e2)
  | Minus (e1, e2)
  | Equal (e1, e2)
  | And (e1, e2)
  | Or (e1, e2)
  | Ge (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Lt (e1, e2) ->
      build_myfun e1 outer;
      build_myfun e2 outer
  | Not e -> build_myfun e outer
  | If (e1, e2, e3, l) ->
      add_myfun l outer;
      build_myfun e1 outer;
      build_myfun e2 outer;
      build_myfun e3 outer
  | Record entries -> List.iter entries ~f:(fun (_, e) -> build_myfun e outer)
  | Projection (e, _) | Inspection (_, e) -> build_myfun e outer
  | LetAssert (_, e1, e2) ->
      build_myfun e1 outer;
      build_myfun e2 outer
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
  incr next_label;
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
  | LetAssert (ident, e1, e2) ->
      let e1' = transform_let e1 in
      let e2' = transform_let e2 in
      LetAssert (ident, e1', e2')
  | _ -> e

(* let rec subst e x e' =
   match e with
   | Let (id, e1, e2, _) ->
       let e1 = subst e1 x e' in
       let e2 = if Stdlib.( = ) id x then e2 else subst e2 id e1 in
       e2
   | Var (id, l) -> if Stdlib.( = ) id x then e' else Var (id, l)
   | Function (id, e, l) ->
       Function (id, (if Stdlib.( = ) x id then e else subst e x e'), l)
   | Appl (e1, e2, l) -> Appl (subst e1 x e', subst e2 x e', l)
   | If (e1, e2, e3, l) -> If (subst e1 x e', subst e2 x e', subst e3 x e', l)
   | Plus (e1, e2) -> Plus (subst e1 x e', subst e2 x e')
   | Minus (e1, e2) -> Minus (subst e1 x e', subst e2 x e')
   | Equal (e1, e2) -> Equal (subst e1 x e', subst e2 x e')
   | And (e1, e2) -> And (subst e1 x e', subst e2 x e')
   | Or (e1, e2) -> Or (subst e1 x e', subst e2 x e')
   | Not e -> Not (subst e x e')
   | _ -> e *)

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
let build_ge e1 e2 = Ge (e1, e2)
let build_gt e1 e2 = Gt (e1, e2)
let build_le e1 e2 = Le (e1, e2)
let build_lt e1 e2 = Lt (e1, e2)
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

let build_letassert ident e1 e2 = LetAssert (ident, e1, e2)
let build_record entries = Record entries
let build_projection e s = Projection (e, Ident s)
let build_inspection s e = Inspection (Ident s, e)
