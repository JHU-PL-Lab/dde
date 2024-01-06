(** AST-related data structures and help functions *)

open Base_quickcheck
open Sexplib.Std
open Core

type ident = Ident of string
[@@deriving show { with_path = false }, quickcheck, compare, sexp, hash]

(** Expressions per paper Fig. 4 *)
type expr =
  | Int of int
  | Bool of bool
  | Fun of ident * expr * int
  | Var of ident * int
  | App of expr * expr * int
  | Plus of expr * expr
  | Minus of expr * expr
  | Mult of expr * expr
  | Eq of expr * expr
  | And of expr * expr
  | Or of expr * expr
  | Ge of expr * expr
  | Gt of expr * expr
  | Le of expr * expr
  | Lt of expr * expr
  | Not of expr
  | If of expr * expr * expr
  | Let of ident * expr * expr * int
  | LetAssert of ident * expr * expr
  | Rec of (ident * expr) list
  | Proj of expr * ident
  | Insp of ident * expr
[@@deriving show { with_path = false }, quickcheck, compare, sexp, hash]

(* Call stack per paper Fig. 4 *)
type sigma = int list
[@@deriving show { with_path = false }, compare, sexp, hash]

(** Result values per paper Fig. 4 *)
type res =
  | IntRes of int
  | BoolRes of bool
  | FunRes of { f : expr; l : int; sigma : int list }
  | RecRes of (ident * res) list
  | PlusRes of res * res
  | MinusRes of res * res
  | MultRes of res * res
  | EqRes of res * res
  | AndRes of res * res
  | OrRes of res * res
  | GeRes of res * res
  | GtRes of res * res
  | LeRes of res * res
  | LtRes of res * res
  | NotRes of res
[@@deriving show { with_path = false }]

(** Result values that may contain free variables, for use in letassert *)
type res_val_fv =
  | IntResFv of int
  | BoolResFv of bool
  | VarResFv of ident
  | EqResFv of res_val_fv * res_val_fv
  | GeResFv of res_val_fv * res_val_fv
  | GtResFv of res_val_fv * res_val_fv
  | LeResFv of res_val_fv * res_val_fv
  | LtResFv of res_val_fv * res_val_fv
  | NotResFv of res_val_fv
  | ProjResFv of res_val_fv * ident
[@@deriving hash, sexp, compare, show { with_path = false }]

(* Table mapping labels to expressions *)
let myexpr = Hashtbl.create (module Int)

(* Table mapping labels to expressions (functions) *)
let myfun = Hashtbl.create (module Int)
let get_myexpr label = Hashtbl.find_exn myexpr label
let add_myexpr label e = Hashtbl.set myexpr ~key:label ~data:e
let get_myfun label = Hashtbl.find myfun label

let add_myfun label outer =
  if Option.is_some outer then
    Hashtbl.set myfun ~key:label ~data:(Option.value_exn outer)

(** Construct a myfun mapping by traversing the AST *)
let rec build_myfun e outer =
  match e with
  | Int _ -> ()
  | Bool _ -> ()
  | Fun (_, e', l) ->
      add_myfun l outer;
      build_myfun e' (Some e)
  | Var (_, l) -> add_myfun l outer
  | App (e1, e2, _)
  | Plus (e1, e2)
  | Minus (e1, e2)
  | Mult (e1, e2)
  | Eq (e1, e2)
  | And (e1, e2)
  | Or (e1, e2)
  | Ge (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Lt (e1, e2) ->
      build_myfun e1 outer;
      build_myfun e2 outer
  | Not e -> build_myfun e outer
  | If (e1, e2, e3) ->
      build_myfun e1 outer;
      build_myfun e2 outer;
      build_myfun e3 outer
  | Rec entries -> List.iter entries ~f:(fun (_, e) -> build_myfun e outer)
  | Proj (e, _) | Insp (_, e) -> build_myfun e outer
  | LetAssert (_, e1, e2) ->
      build_myfun e1 outer;
      build_myfun e2 outer
  | Let (_, e1, e2, _) ->
      build_myfun e1 outer;
      build_myfun e2 outer

(* Next int to use for labeling AST nodes *)
let next_label = ref 0

let get_next_label () =
  let l = !next_label in
  incr next_label;
  l

(** Reset the tables and the counter *)
let clean_up () =
  Hashtbl.clear myexpr;
  Hashtbl.clear myfun;
  next_label := 0

(* Functions used by the parser to build AST nodes *)
let build_int i = Int i
let build_bool b = Bool b

let build_function ident e =
  let label = get_next_label () in
  let labeled_function = Fun (ident, e, label) in
  add_myexpr label labeled_function;
  labeled_function

let build_appl e1 e2 =
  let label = get_next_label () in
  let labeled_appl = App (e1, e2, label) in
  add_myexpr label labeled_appl;
  labeled_appl

let build_var ident =
  let label = get_next_label () in
  let labeled_var = Var (ident, label) in
  add_myexpr label labeled_var;
  labeled_var

let build_plus e1 e2 = Plus (e1, e2)
let build_minus e1 e2 = Minus (e1, e2)
let build_mult e1 e2 = Mult (e1, e2)
let build_eq e1 e2 = Eq (e1, e2)
let build_and e1 e2 = And (e1, e2)
let build_or e1 e2 = Or (e1, e2)
let build_ge e1 e2 = Ge (e1, e2)
let build_gt e1 e2 = Gt (e1, e2)
let build_le e1 e2 = Le (e1, e2)
let build_lt e1 e2 = Lt (e1, e2)
let build_not e = Not e
let build_if e1 e2 e3 = If (e1, e2, e3)

let build_let id e1 e2 =
  let label = get_next_label () in
  let labeled_let = Let (id, e1, e2, label) in
  add_myexpr label labeled_let;
  labeled_let

let build_letassert id e1 e2 = LetAssert (id, e1, e2)
let build_record entries = Rec entries
let build_projection e s = Proj (e, Ident s)
let build_inspection s e = Insp (Ident s, e)

(** Substitute away let bindings ahead of time *)
let rec subst_let x e' e =
  match e with
  | Let (id, e1, e2, _) ->
      let e1 = subst_let x e' e1 in
      let e2 =
        if Option.is_some x && compare_ident id (Option.value_exn x) = 0 then e2
        else subst_let x e' e2
      in
      subst_let (Some id) (Some e1) e2
  | Var (id, _) ->
      if Option.is_some x && compare_ident id (Option.value_exn x) = 0 then
        Option.value_exn e'
      else e
  | Fun (id, e1, l) ->
      Fun
        ( id,
          (if Option.is_some x && compare_ident id (Option.value_exn x) = 0 then
             e1
           else subst_let x e' e1),
          l )
  | App (e1, e2, l) ->
      let e = App (subst_let x e' e1, subst_let x e' e2, l) in
      (* Only sync expression of label here as function application is
         the only expression looked up by its label, besides a variable *)
      add_myexpr l e;
      e
  | If (e1, e2, e3) ->
      If (subst_let x e' e1, subst_let x e' e2, subst_let x e' e3)
  | Plus (e1, e2) -> Plus (subst_let x e' e1, subst_let x e' e2)
  | Minus (e1, e2) -> Minus (subst_let x e' e1, subst_let x e' e2)
  | Mult (e1, e2) -> Mult (subst_let x e' e1, subst_let x e' e2)
  | Eq (e1, e2) -> Eq (subst_let x e' e1, subst_let x e' e2)
  | And (e1, e2) -> And (subst_let x e' e1, subst_let x e' e2)
  | Or (e1, e2) -> Or (subst_let x e' e1, subst_let x e' e2)
  | Ge (e1, e2) -> Ge (subst_let x e' e1, subst_let x e' e2)
  | Gt (e1, e2) -> Gt (subst_let x e' e1, subst_let x e' e2)
  | Le (e1, e2) -> Le (subst_let x e' e1, subst_let x e' e2)
  | Lt (e1, e2) -> Lt (subst_let x e' e1, subst_let x e' e2)
  | Not e1 -> Not (subst_let x e' e1)
  | Rec entries ->
      Rec (List.map ~f:(fun (x1, e1) -> (x1, subst_let x e' e1)) entries)
  | Proj (e1, id) -> Proj (subst_let x e' e1, id)
  | Insp (id, e1) -> Insp (id, subst_let x e' e1)
  | LetAssert (id, e1, e2) -> LetAssert (id, subst_let x e' e1, e2)
  | Int _ | Bool _ -> e

(** An alternative that transforms let bindings
    into function applications (not used) *)
let rec trans_let_app e =
  match e with
  | Int _ | Bool _ | Var _ -> e
  | Fun (ident, e, l) ->
      let e' = trans_let_app e in
      let f = Fun (ident, e', l) in
      add_myexpr l f;
      f
  | Let (ident, e1, e2, let_l) ->
      let fun_l = get_next_label () in
      let e2' = trans_let_app e2 in
      let f = Fun (ident, e2', fun_l) in
      add_myexpr fun_l f;
      let e1' = trans_let_app e1 in
      let appl = App (f, e1', let_l) in
      add_myexpr let_l appl;
      appl
  | App (e1, e2, l) ->
      let e1' = trans_let_app e1 in
      let e2' = trans_let_app e2 in
      let appl = App (e1', e2', l) in
      add_myexpr l appl;
      appl
  | LetAssert (id, e1, e2) ->
      let e1' = trans_let_app e1 in
      let e2' = trans_let_app e2 in
      LetAssert (id, e1', e2')
  | If (e1, e2, e3) ->
      let e1' = trans_let_app e1 in
      let e2' = trans_let_app e2 in
      let e3' = trans_let_app e3 in
      If (e1', e2', e3')
  | Plus (e1, e2) -> Plus (trans_let_app e1, trans_let_app e2)
  | Minus (e1, e2) -> Minus (trans_let_app e1, trans_let_app e2)
  | Mult (e1, e2) -> Mult (trans_let_app e1, trans_let_app e2)
  | Eq (e1, e2) -> Eq (trans_let_app e1, trans_let_app e2)
  | Ge (e1, e2) -> Ge (trans_let_app e1, trans_let_app e2)
  | Gt (e1, e2) -> Gt (trans_let_app e1, trans_let_app e2)
  | Le (e1, e2) -> Le (trans_let_app e1, trans_let_app e2)
  | Lt (e1, e2) -> Lt (trans_let_app e1, trans_let_app e2)
  | And (e1, e2) -> And (trans_let_app e1, trans_let_app e2)
  | Or (e1, e2) -> Or (trans_let_app e1, trans_let_app e2)
  | Not e -> Not (trans_let_app e)
  | Rec es -> Rec (List.map es ~f:(fun (id, e) -> (id, trans_let_app e)))
  | Proj (e, id) -> Proj (trans_let_app e, id)
  | Insp (id, e) -> Insp (id, trans_let_app e)
