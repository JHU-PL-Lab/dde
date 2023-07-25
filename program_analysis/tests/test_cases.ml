open Program_analysis.Solver

let ri = zconst "r" isort
let rb = zconst "r" bsort

type test_case = {
  prog : string;
  verif : Z3.FuncDecl.func_decl -> Z3.Expr.expr;
}

let basic =
  [|
    "letassert x = 1 in true";
    "letassert x = (fun x -> x) 1 in x = 1";
    "letassert x = (fun y -> 1 + y) 2 in x = 3";
  |]

let nonlocal_lookup =
  [|
    "letassert x = (fun x -> (fun y -> x + y) 2) 1 in x = 3";
    "letassert x = ((fun x -> fun y -> x + y) 1) 2 in x = 3";
    "letassert x = (fun x -> (fun y -> (fun z -> x + y + z) 2) 1) 3 in x = 6";
  |]

let local_stitching =
  [|
    "letassert x =\n\
     (let add = (fun num -> fun n -> n + num) in\n\
     let add1 = add 1 in\n\
     let add1' = (fun n -> add1 n) in\n\
     add1 1 + add1' 1)\n\
     in x = 4";
    "letassert x =\n\
     (let add = (fun f -> fun g -> fun x -> f g x) in\n\
     let add1 = add (fun z -> fun n -> z n + 2) in\n\
     let add2 = add1 (fun y -> y + 1) in\n\
     add2 0)\n\
     in x = 3";
  |]

let conditional =
  [|
    "letassert x = (fun id -> id 10) (fun n -> if n = 0 then 0 else 1 + (n - \
     1)) in x = 10";
    "letassert x = if true then 1 else 2 in x = 1";
    "letassert x = (fun x -> (if true then (fun y -> y) else (fun z -> z)) x) \
     1 in x = 1";
    "letassert x = if true then (if true then (if true then 1 else 2) else 3) \
     else 4 in x = 1";
    "letassert x = if (if (if true and false then false else true) then false \
     else true) then true else false in not x";
  |]

let currying =
  [|
    "letassert x = let add = (fun num -> fun n -> n + num) in let add1 = add 1 \
     in add1 2 in x = 3";
    "letassert x = (fun add -> (fun add1 -> (fun add2 -> add1 2) (add 2)) (add \
     1)) (fun num -> fun n -> n + num) in x = 3";
    "letassert x = let add = (fun num -> fun n -> n + num) in let add2 = add 2 \
     in add2 1 in x = 3";
    "letassert x = let add = (fun num -> fun n -> n + num) in let add1 = add 1 \
     in let add2 = add 2 in add1 2 + add2 1 in x = 6";
    "letassert x =\n\
     let add = (fun num -> fun n -> n + num) in\n\
     let add1 = add 1 in\n\
     let add2 = add 2 in\n\
     let add3 = add 3 in\n\
     let add4 = add 4 in\n\
     let add5 = add 5 in\n\
     add1 1 + add2 1 + add3 1 + add4 1 + add5 1 in\n\
     x = 20";
  |]

let recursion =
  [|
    (* (1 + (1 + (1 + ((1 + stub) | 0)))) *)
    (* ((((10 - 1) - 1) | ((((10 - 1) - 1) | (stub - 1)) - 1)) = 0) *)
    "letassert x = let id = fun self -> fun n -> if n = 0 then 0 else 1 + self \
     self (n - 1) in id id 10 in x >= 2";
    (* (1 + (1 + (1 + ((1 + stub) | 0)))) *)
    "letassert x = (let id = fun self -> fun n -> if n = 10 then true else \
     false or self self (n + 1) in id id 0) in x";
    (* (1 + (1 + (1 + (1 + stub)))) *)
    (* ((((-1 - 1) - 1) | ((((-1 - 1) - 1) | (stub - 1)) - 1)) = 0) *)
    "letassert _x = (let id = fun self -> fun n -> if n = 0 then 0 else 1 + \
     self self (n - 1) in id id (-1)) in false";
    (* TODO: check divergence before CHCs *)
    (* "letassert _x = ((fun self -> fun n -> self self n) (fun self -> fun n -> \
       self self n) 0) in false"; *)
  |]

(** Church numerals *)

let zero = "(fun f -> fun x -> x)"
let one = "(fun f -> f)"
let succ = "(fun c -> fun f -> fun x -> f (c f x))"
let add = "(fun m -> fun n -> fun f -> fun x -> m f (n f x))"
let mul = "(fun m -> fun n -> fun f -> fun x -> m (n f) x)"
let unchurch = "(fun f -> f (function x -> x + 1) 0)"

let church n =
  let rec aux n =
    match n with 0 -> zero | n -> succ ^ "(" ^ aux (n - 1) ^ ")"
  in
  "(" ^ aux n ^ ")"

let church_basic =
  [|
    "letassert x = " ^ unchurch ^ church 1 ^ " in x = 1";
    "letassert x = " ^ unchurch ^ church 2 ^ " in x = 2";
    "letassert x = " ^ unchurch ^ church 3 ^ " in x = 3";
    "letassert x = " ^ unchurch ^ church 4 ^ " in x = 4";
  |]

let church_binop =
  [| "letassert x = " ^ unchurch ^ "(" ^ add ^ zero ^ one ^ ") in x = 1" |]
