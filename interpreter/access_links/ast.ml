open Core

type ident = Ident of string
[@@deriving show { with_path = false }, compare, sexp, hash]

type expr =
  | ALInt of int
  | ALBool of bool
  | ALFun of ident * expr
  | ALVar of ident * int
  | ALApp of expr * expr
  | ALPlus of expr * expr
  | ALMinus of expr * expr
  | ALMult of expr * expr
  | ALEq of expr * expr
  | ALAnd of expr * expr
  | ALOr of expr * expr
  | ALGe of expr * expr
  | ALGt of expr * expr
  | ALLe of expr * expr
  | ALLt of expr * expr
  | ALNot of expr
  | ALIf of expr * expr * expr
    (* | LetAssert of ident * expr * expr
       | Record of (ident * expr) list
       | Projection of expr * ident
       | Inspection of ident * expr *)
[@@deriving show { with_path = false }, compare, sexp, hash]

let build_fun id e = ALFun (id, e)
let build_int i = ALInt i
let build_bool b = ALBool b
let build_var id = ALVar (id, -1)
let build_app e1 e2 = ALApp (e1, e2)
let build_plus e1 e2 = ALPlus (e1, e2)
let build_minus e1 e2 = ALMinus (e1, e2)
let build_mult e1 e2 = ALMult (e1, e2)
let build_eq e1 e2 = ALEq (e1, e2)
let build_ge e1 e2 = ALGe (e1, e2)
let build_gt e1 e2 = ALGt (e1, e2)
let build_le e1 e2 = ALLe (e1, e2)
let build_lt e1 e2 = ALLt (e1, e2)
let build_and e1 e2 = ALAnd (e1, e2)
let build_or e1 e2 = ALOr (e1, e2)
let build_not e = ALNot e
let build_if e1 e2 e3 = ALIf (e1, e2, e3)
let build_let id e1 e2 = ALApp (ALFun (id, e2), e1)

let rec assign_depth ?(d = 0) ?(m = String.Map.empty) e =
  match e with
  | ALInt _ | ALBool _ -> e
  | ALVar ((Ident x as id), _) -> ALVar (id, d - Map.find_exn m x)
  | ALFun ((Ident x as id), e) ->
      let d = d + 1 in
      ALFun
        (id, assign_depth e ~d ~m:(Map.add_exn (Map.remove m x) ~key:x ~data:d))
  | ALApp (e1, e2) -> ALApp (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALPlus (e1, e2) -> ALPlus (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALMinus (e1, e2) -> ALMinus (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALMult (e1, e2) -> ALMinus (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALEq (e1, e2) -> ALEq (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALGe (e1, e2) -> ALGe (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALGt (e1, e2) -> ALGt (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALLe (e1, e2) -> ALLe (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALLt (e1, e2) -> ALLt (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALAnd (e1, e2) -> ALAnd (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALOr (e1, e2) -> ALOr (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | ALNot e1 -> ALNot (assign_depth e ~d ~m)
  | ALIf (e1, e2, e3) ->
      ALIf (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m, assign_depth e3 ~d ~m)
