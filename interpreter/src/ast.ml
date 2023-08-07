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
  | EqOp of result_value * result_value
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
  | PlusOpFv of result_value_fv * result_value_fv
  | MinusOpFv of result_value_fv * result_value_fv
  | EqOpFv of result_value_fv * result_value_fv
  | AndOpFv of result_value_fv * result_value_fv
  | OrOpFv of result_value_fv * result_value_fv
  | GeOpFv of result_value_fv * result_value_fv
  | GtOpFv of result_value_fv * result_value_fv
  | LeOpFv of result_value_fv * result_value_fv
  | LtOpFv of result_value_fv * result_value_fv
  | NotOpFv of result_value_fv
(* TODO: pretty print *)

(** result values that may contain free variables *)
and result_value_fv =
  | IntResultFv of int
  | BoolResultFv of bool
  | VarResultFv of ident
  | OpResultFv of op_result_value_fv
  | FunResultFv
  | RecordResultFv of (ident * result_value_fv) list
  | ProjectionResultFv of result_value_fv * ident
  | InspectionResultFv
[@@deriving hash, sexp, compare, show { with_path = false }]

type fbtype = TArrow of fbtype * fbtype | TVar of string
[@@coverage off] [@@deriving show { with_path = false }]

let myexpr = Hashtbl.create (module Int)
let myfun = Hashtbl.create (module Int)
let get_myexpr label = Hashtbl.find_exn myexpr label
let add_myexpr label e = Hashtbl.set myexpr ~key:label ~data:e
let get_myfun label = Hashtbl.find myfun label

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
      (* TODO: likely don't need this l *)
      add_myfun l outer;
      build_myfun e1 outer;
      build_myfun e2 outer;
      build_myfun e3 outer
  | Record entries -> List.iter entries ~f:(fun (_, e) -> build_myfun e outer)
  | Projection (e, _) | Inspection (_, e) -> build_myfun e outer
  | LetAssert (_, e1, e2) ->
      build_myfun e1 outer;
      build_myfun e2 outer
  | Let (_, e1, e2, _) ->
      build_myfun e1 outer;
      build_myfun e2 outer

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

let build_let id e1 e2 =
  let label = get_next_label () in
  let labeled_let = Let (id, e1, e2, label) in
  add_myexpr label labeled_let;
  labeled_let

let build_letassert id e1 e2 = LetAssert (id, e1, e2)
let build_record entries = Record entries
let build_projection e s = Projection (e, Ident s)
let build_inspection s e = Inspection (Ident s, e)

let rec trans_let x e' e =
  match e with
  | Let (id, e1, e2, _) ->
      let e1 = trans_let x e' e1 in
      let e2 =
        if Option.is_some x && Stdlib.( = ) id (Option.value_exn x) then e2
        else trans_let x e' e2
      in
      trans_let (Some id) (Some e1) e2
  | Var (id, _) ->
      if Option.is_some x && Stdlib.( = ) id (Option.value_exn x) then
        Option.value_exn e'
      else e
  | Function (id, e1, l) ->
      Function
        ( id,
          (if Option.is_some x && Stdlib.( = ) id (Option.value_exn x) then e1
           else trans_let x e' e1),
          l )
  | Appl (e1, e2, l) ->
      let e = Appl (trans_let x e' e1, trans_let x e' e2, l) in
      (* only sync expression of label here as function application is
         the only expression looked up by its label, besides a variable *)
      add_myexpr l e;
      e
  | If (e1, e2, e3, l) ->
      If (trans_let x e' e1, trans_let x e' e2, trans_let x e' e3, l)
  | Plus (e1, e2) -> Plus (trans_let x e' e1, trans_let x e' e2)
  | Minus (e1, e2) -> Minus (trans_let x e' e1, trans_let x e' e2)
  | Equal (e1, e2) -> Equal (trans_let x e' e1, trans_let x e' e2)
  | And (e1, e2) -> And (trans_let x e' e1, trans_let x e' e2)
  | Or (e1, e2) -> Or (trans_let x e' e1, trans_let x e' e2)
  | Ge (e1, e2) -> Ge (trans_let x e' e1, trans_let x e' e2)
  | Gt (e1, e2) -> Gt (trans_let x e' e1, trans_let x e' e2)
  | Le (e1, e2) -> Le (trans_let x e' e1, trans_let x e' e2)
  | Lt (e1, e2) -> Lt (trans_let x e' e1, trans_let x e' e2)
  | Not e1 -> Not (trans_let x e' e1)
  | Record entries ->
      Record (List.map ~f:(fun (x1, e1) -> (x1, trans_let x e' e1)) entries)
  | Projection (e1, id) -> Projection (trans_let x e' e1, id)
  | Inspection (id, e1) -> Inspection (id, trans_let x e' e1)
  | LetAssert (id, e1, e2) -> LetAssert (id, trans_let x e' e1, e2)
  | Int _ | Bool _ -> e
