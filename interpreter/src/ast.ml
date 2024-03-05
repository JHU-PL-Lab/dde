(** AST-related data structures and help functions *)

open Base_quickcheck
open Sexplib.Std
open Core
open Exns

let ff = Format.fprintf

module Ident = struct
  module T = struct
    type t = Ident of string [@@deriving compare, sexp]

    let pp fmt (Ident x) = ff fmt "%s" x
  end

  include T
  include Comparable.Make (T)
end

(** Expressions per paper Fig. 4 *)
module Expr = struct
  type t =
    | Int of int
    | Bool of bool
    | Fun of Ident.t * t * t list
    | Var of Ident.t * int
    | App of t * t * int
    | Plus of t * t
    | Minus of t * t
    | Mult of t * t
    | Eq of t * t
    | And of t * t
    | Or of t * t
    | Ge of t * t
    | Gt of t * t
    | Le of t * t
    | Lt of t * t
    | Not of t
    | If of t * t * t
    | Let of Ident.t * t * t * int
    | LetAssert of Ident.t * t * t
    | Rec of (Ident.t * t) list
    | Proj of t * Ident.t
    | Insp of Ident.t * t
  [@@deriving compare, sexp]

  let paren_if cond pp fmt e =
    if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

  let is_compound_expr = function Int _ | Bool _ | Var _ -> false | _ -> true

  let is_compound_exprL = function
    | Int _ | Bool _ | App _ -> false
    | other -> is_compound_expr other

  let rec pp fmt = function
    | Int i -> ff fmt "%d" i
    | Bool b -> ff fmt "%b" b
    (* TODO: pp call stack *)
    | Fun (Ident i, x, _) -> ff fmt "@[<hv>fun %s ->@;<1 2>%a@]" i pp x
    (* | Fun (Ident i, x, l) ->
        ff fmt "@[<hv>fun %s ->@;<1 2>%a[@%d]@]" i pp x (List.length l) *)
    | Var (id, _) -> ff fmt "%a" Ident.pp id
    (* | Var (id, idx) -> ff fmt "%a@%d" Ident.pp id idx *)
    | App (e1, e2, _) ->
        ff fmt "%a %a"
          (paren_if is_compound_exprL pp)
          e1
          (paren_if is_compound_expr pp)
          e2
    (* | App (e1, e2, l) ->
        ff fmt "(%a %a)@%d"
          (paren_if is_compound_exprL pp)
          e1
          (paren_if is_compound_expr pp)
          e2 l *)
    | Plus (e1, e2) -> ff fmt "(%a + %a)" pp e1 pp e2
    | Minus (e1, e2) -> ff fmt "(%a - %a)" pp e1 pp e2
    | Mult (e1, e2) -> ff fmt "(%a * %a)" pp e1 pp e2
    | Eq (e1, e2) -> ff fmt "(%a = %a)" pp e1 pp e2
    | And (e1, e2) -> ff fmt "(%a and %a)" pp e1 pp e2
    | Or (e1, e2) -> ff fmt "(%a or %a)" pp e1 pp e2
    | Ge (e1, e2) -> ff fmt "(%a >= %a)" pp e1 pp e2
    | Gt (e1, e2) -> ff fmt "(%a > %a)" pp e1 pp e2
    | Le (e1, e2) -> ff fmt "(%a <= %a)" pp e1 pp e2
    | Lt (e1, e2) -> ff fmt "(%a < %a)" pp e1 pp e2
    | Not e1 -> ff fmt "(not %a)" pp e1
    | If (e1, e2, e3) ->
        ff fmt "@[<hv>if %a then@;<1 2>%a@;<1 0>else@;<1 2>%a@]" pp e1 pp e2 pp
          e3
    | Let (Ident i, e1, e2, _) ->
        ff fmt "@[<hv>let %s =@;<1 4>%a@;<1 0>in@;<1 4>%a@]" i pp e1 pp e2
    | LetAssert (Ident i, e1, e2) ->
        ff fmt "@[<hv>letassert %s =@;<1 4>%a@;<1 0>in@;<1 4>%a@]" i pp e1 pp e2
    | Rec entries ->
        ff fmt
          (if List.length entries = 0 then "{%a}" else "{ %a }")
          pp_record entries
    | Proj (e, Ident x) -> ff fmt "(%a.%s)" pp e x
    | Insp (Ident x, e) -> ff fmt "(%s in %a)" x pp e

  and pp_record fmt = function
    | [] -> ()
    | [ (Ident x, e) ] -> ff fmt "%s = %a" x pp e
    | (Ident x, e) :: rest -> ff fmt "%s = %a; %a" x pp e pp_record rest
end

(* Call stack per paper Fig. 4 *)
type sigma = int list
[@@deriving show { with_path = false }, compare, sexp, hash]

(** Result values per paper Fig. 4 *)
module Res = struct
  type t =
    | IntRes of int
    | BoolRes of bool
    | FunRes of Expr.t * sigma
    | RecRes of (Ident.t * t) list
    | PlusRes of t * t
    | MinusRes of t * t
    | MultRes of t * t
    | EqRes of t * t
    | AndRes of t * t
    | OrRes of t * t
    | GeRes of t * t
    | GtRes of t * t
    | LeRes of t * t
    | LtRes of t * t
    | NotRes of t

  let rec pp fmt = function
    | IntRes x -> ff fmt "%d" x
    | BoolRes b -> ff fmt "%b" b
    | FunRes (f, _) -> Expr.pp fmt f
    | RecRes es ->
        ff fmt (if List.length es = 0 then "{%a}" else "{ %a }") pp_rec_res es
    | PlusRes (r1, r2) -> ff fmt "%a + %a" pp r1 pp r2
    | MinusRes (r1, r2) -> ff fmt "%a - %a" pp r1 pp r2
    | MultRes (r1, r2) -> ff fmt "%a * %a" pp r1 pp r2
    | EqRes (r1, r2) -> ff fmt "%a = %a" pp r1 pp r2
    | AndRes (r1, r2) -> ff fmt "%a and %a" pp r1 pp r2
    | OrRes (r1, r2) -> ff fmt "%a or %a" pp r1 pp r2
    | GeRes (r1, r2) -> ff fmt "%a >= %a" pp r1 pp r2
    | GtRes (r1, r2) -> ff fmt "%a > %a" pp r1 pp r2
    | LeRes (r1, r2) -> ff fmt "%a <= %a" pp r1 pp r2
    | LtRes (r1, r2) -> ff fmt "%a < %a" pp r1 pp r2
    | NotRes r1 -> ff fmt "not %a" pp r1

  and pp_rec_res fmt = function
    | [] -> ()
    | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x pp v
    | (Ident x, v) :: rest ->
        Format.fprintf fmt "%s = %a; %a" x pp v pp_rec_res rest
end

(** Result values that may contain free variables, for use in letassert *)
module Res_fv = struct
  type t =
    | IntResFv of int
    | BoolResFv of bool
    | VarResFv of Ident.t
    | EqResFv of t * t
    | GeResFv of t * t
    | GtResFv of t * t
    | LeResFv of t * t
    | LtResFv of t * t
    | NotResFv of t
    | ProjResFv of t * Ident.t
  [@@deriving sexp, compare]

  let rec pp fmt = function
    | IntResFv i -> ff fmt "%d" i
    | BoolResFv b -> ff fmt "%b" b
    | VarResFv (Ident x) -> ff fmt "%s" x
    | GeResFv (v1, v2) -> ff fmt "%a > %a" pp v1 pp v2
    | _ -> ()
end

(* Table mapping labels to expressions *)
let myexpr = Hashtbl.create (module Int)

(* Table mapping labels to expressions (functions) *)
let get_myexpr label = Hashtbl.find_exn myexpr label
let add_myexpr label e = Hashtbl.set myexpr ~key:label ~data:e

let string_of_table tbl which =
  Hashtbl.to_alist tbl
  |> List.sort ~compare:(fun (k1, v1) (k2, v2) -> Int.ascending k1 k2)
  |> List.map ~f:(fun (k, v) -> Format.asprintf "%d -> %a" k Expr.pp v)
  |> String.concat ~sep:"\n"
  |> fun content ->
  Format.sprintf "=== %s table ===\n%s\n*** %s table ***\n" which content which

(* Next int to use for labeling AST nodes *)
let next_label = ref 0

let get_next_label () =
  let l = !next_label in
  incr next_label;
  l

(** Reset the tables and the counter *)
let clean_up () =
  Hashtbl.clear myexpr;
  next_label := 0

open Expr

(* Functions used by the parser to build AST nodes *)
let build_int i = Int i
let build_bool b = Bool b

(* Placeholder label to be filled in later *)
let build_function id e = Fun (id, e, [])

let build_app e1 e2 =
  let l = get_next_label () in
  let app = App (e1, e2, l) in
  add_myexpr l app;
  app

(* Placeholder de Bruijn index to be filled in later *)
let build_var id = Var (id, 0)
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
let build_let id e1 e2 = Let (id, e1, e2, 0)
let build_letassert id e1 e2 = LetAssert (id, e1, e2)
let build_rec entries = Rec entries
let build_proj e s = Proj (e, Ident s)
let build_insp s e = Insp (Ident s, e)

let rec assign_index ?(i = 0) ?(intros = String.Map.empty) expr =
  match expr with
  | Int _ | Bool _ -> expr
  | Var ((Ident x as id), _) -> Var (id, i - Map.find_exn intros x)
  | Fun ((Ident x as id), e, vars) ->
      Fun
        ( id,
          assign_index e ~i:(i + 1)
            ~intros:(Map.add_exn (Map.remove intros x) ~key:x ~data:(i + 1)),
          vars )
  | App (e1, e2, l) ->
      let app =
        App (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros, l)
      in
      add_myexpr l app;
      app
  | Plus (e1, e2) ->
      Plus (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Minus (e1, e2) ->
      Minus (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Mult (e1, e2) ->
      Mult (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Eq (e1, e2) -> Eq (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Ge (e1, e2) -> Ge (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Gt (e1, e2) -> Gt (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Le (e1, e2) -> Le (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Lt (e1, e2) -> Lt (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | And (e1, e2) -> And (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Or (e1, e2) -> Or (assign_index e1 ~i ~intros, assign_index e2 ~i ~intros)
  | Not e -> Not (assign_index e ~i ~intros)
  | If (e1, e2, e3) ->
      If
        ( assign_index e1 ~i ~intros,
          assign_index e2 ~i ~intros,
          assign_index e3 ~i ~intros )
  | Rec es ->
      Rec (List.map es ~f:(fun (id, e) -> (id, assign_index e ~i ~intros)))
  | Proj (e, id) -> Proj (assign_index e ~i ~intros, id)
  | Insp (id, e) -> Insp (id, assign_index e ~i ~intros)
  | LetAssert (id, e1, e2) -> LetAssert (id, assign_index e1 ~i ~intros, e2)
  | Let _ -> raise Unreachable

let rec scope_vars ?(vs = []) expr : Expr.t =
  match expr with
  | Int _ | Bool _ | Var _ -> expr
  | Fun (id, e, _) ->
      let vs' =
        vs
        (* Remove vars shadowed by id *)
        |> List.filter ~f:(function
             | Var (id', _) -> Ident.(id <> id')
             | _ -> true)
        (* Increment the rest to reflect the incremented depth *)
        |> List.map ~f:(function
             | Var (id, idx) -> Var (id, idx + 1)
             | _ -> raise Unreachable)
        |> List.cons (Var (id, 0))
      in
      Fun (id, scope_vars e ~vs:vs', vs')
  | App (e1, e2, l) ->
      let app = App (scope_vars e1 ~vs, scope_vars e2 ~vs, l) in
      add_myexpr l app;
      app
  | Plus (e1, e2) -> Plus (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Minus (e1, e2) -> Minus (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Mult (e1, e2) -> Mult (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Eq (e1, e2) -> Eq (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Ge (e1, e2) -> Ge (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Gt (e1, e2) -> Gt (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Le (e1, e2) -> Le (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Lt (e1, e2) -> Lt (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | And (e1, e2) -> And (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Or (e1, e2) -> Or (scope_vars e1 ~vs, scope_vars e2 ~vs)
  | Not e -> Not (scope_vars e ~vs)
  | Proj (e, id) -> Proj (scope_vars e ~vs, id)
  | Insp (id, e) -> Insp (id, scope_vars e ~vs)
  | If (e1, e2, e3) ->
      If (scope_vars e1 ~vs, scope_vars e2 ~vs, scope_vars e3 ~vs)
  | Rec es -> Rec (List.map es ~f:(fun (id, e) -> (id, scope_vars e ~vs)))
  | LetAssert (id, e1, e2) -> LetAssert (id, scope_vars e1 ~vs, e2)
  | Let _ -> raise Unreachable

(** Substitute away let bindings ahead of time *)
let rec subst_let x e' e =
  match e with
  | Int _ | Bool _ -> e
  | Let (id, e1, e2, _) ->
      let e1 = subst_let x e' e1 in
      let e2 =
        if Option.is_some x && Ident.(id = Option.value_exn x) then e2
        else subst_let x e' e2
      in
      subst_let (Some id) (Some e1) e2
  | Var (id, _) ->
      if Option.is_some x && Ident.(id = Option.value_exn x) then
        Option.value_exn e'
      else e
  | Fun (id, e1, vars) ->
      Fun
        ( id,
          (if Option.is_some x && Ident.(id = Option.value_exn x) then e1
           else subst_let x e' e1),
          vars )
  | App (e1, e2, l) -> App (subst_let x e' e1, subst_let x e' e2, l)
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
  | Not e -> Not (subst_let x e' e)
  | Rec entries ->
      Rec (List.map ~f:(fun (x1, e1) -> (x1, subst_let x e' e1)) entries)
  | Proj (e, id) -> Proj (subst_let x e' e, id)
  | Insp (id, e) -> Insp (id, subst_let x e' e)
  | LetAssert (id, e1, e2) -> LetAssert (id, subst_let x e' e1, e2)

(** An alternative that transforms let bindings
    into function applications (not used) *)
let rec trans_let_app e =
  match e with
  | Int _ | Bool _ | Var _ -> e
  | Fun (id, e, sv) -> Fun (id, trans_let_app e, sv)
  | Let (id, e1, e2, _) ->
      let l = get_next_label () in
      let app = App (Fun (id, trans_let_app e2, []), trans_let_app e1, l) in
      add_myexpr l app;
      app
  | App (e1, e2, l) -> App (trans_let_app e1, trans_let_app e2, l)
  | LetAssert (id, e1, e2) -> LetAssert (id, trans_let_app e1, trans_let_app e2)
  | If (e1, e2, e3) -> If (trans_let_app e1, trans_let_app e2, trans_let_app e3)
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
