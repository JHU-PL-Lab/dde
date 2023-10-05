open Core
open Program_analysis.Solver

let ri = zconst "r" isort
let rb = zconst "r" bsort

type test_case = {
  prog : string;
  verif : Z3.FuncDecl.func_decl -> Z3.Expr.expr;
}

let read_input file_name =
  In_channel.read_all
    (Format.sprintf
       "/Users/robertzhang/projects/research/dde/program_analysis/tests/inputs/%s"
       file_name)

let read_output file_name =
  In_channel.read_all
    (Format.sprintf
       "/Users/robertzhang/projects/research/dde/program_analysis/tests/outputs/%s"
       file_name)

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

let rec_eg_5 =
  "let f = fun self -> fun x -> (fun y -> if x and y then true else if x and \
   not y then not (self self true true) else if not x and y then self self \
   true false else self self false true) in f f "

let rec_eg_6 =
  "let f = (fun x -> fun dummy -> x) in let loop = fun self -> fun x -> let r \
   = f x in if x = 1 then r 1 else if x = 0 then self self 1 else self self 0 \
   in loop loop "

(* (((1 + ((1 + (((1 + ((stub@3)^3)^5) | 0))^5))^5))^12)^13
   (((1 + ((1 + (((1 + stub@5) | 0))^5))^5))^12)^13 *)

let recursion =
  [|
    (* (1 + (1 + (1 + ((1 + stub) | 0)))) *)
    (* ((((10 - 1) - 1) | ((((10 - 1) - 1) | (stub - 1)) - 1)) = 0) *)
    "letassert x = let id = fun self -> fun n -> if n = 0 then 0 else 1 + self \
     self (n - 1) in id id 10 in x >= 2";
    (* (1 + (1 + (1 + ((1 + stub) | 0)))) *)
    "letassert x = let id = fun self -> fun n -> if n = 10 then true else \
     false or self self (n + 1) in id id 0 in x";
    (* (1 + (1 + (1 + (1 + stub)))) *)
    (* ((((-1 - 1) - 1) | ((((-1 - 1) - 1) | (stub - 1)) - 1)) = 0) *)
    "letassert _x = let id = fun self -> fun n -> if n = 0 then 0 else 1 + \
     self self (n - 1) in id id (-1) in false";
    (* TODO: check divergence before CHCs *)
    (* "letassert _x = ((fun self -> fun n -> self self n) (fun self -> fun n -> \
       self self n) 0) in false"; *)
    "letassert x = let id = fun self -> fun n -> if n > 0 then 1 + self self \
     (n - 1) else 0 in id id 10 in x >= 2";
    "letassert x = let id = fun self -> fun n -> if n > 0 then 1 + self self \
     (n - 1) else 0 in id id (-1) in x = 0";
    (* tests adapted from standard PA *)
    "letassert x = " ^ rec_eg_5 ^ "true true in x";
    (* TODO: solver gives unknown *)
    rec_eg_5 ^ "true false";
    "letassert x = let f = (fun x -> (fun y -> y) x) in let repeat = fun self \
     -> fun acc -> if acc then true else self self (self self (f true)) in \
     repeat repeat true in x";
    "letassert x = let f = (fun x -> fun dummy -> x) in let loop = fun self -> \
     fun x -> let r = (f x) in if x then r 0 else (self self true) in (loop \
     loop false) in x";
    "letassert x = " ^ rec_eg_6 ^ "0 in x >= 1";
    "letassert x = " ^ rec_eg_6 ^ "1 in x >= 1";
    "letassert x = " ^ rec_eg_6 ^ "(0 - 1) in x >= 1";
    (* "let fib = (fun n -> if n < 2 then 1 else let go = (fun self -> fun i -> \
       fun prev -> fun prevprev -> let res = (prev + prevprev) in if i = 0 then \
       res else self self (i - 1) res prev) in go go (n - 2) 1 1) in fib 4"; *)
    "letassert x = let fib = fun self -> fun n -> if n <= 1 then n else self \
     self (n - 1) + self self (n - 2) in fib fib 4 in x >= 0";
    (* "let fib = fun n -> fun self -> if n <= 1 then n else self (n - 1) self + \
       self (n - 2) self in fib 4 fib"; *)
    (* "let nonsense = fun self -> fun n -> if (self self n) = 0 then 1 else 0 in \
       nonsense nonsense 0"; *)
    "letassert x = let id = fun self -> fun n -> if n = 0 then 0 else 1 + (fun \
     _ -> self self (n - 1)) 0 in id id 10 in x >= 2";
  |]

let adapted =
  [|
    read_input "facehugger.ml";
    read_input "blur.ml";
    read_input "mj09.ml";
    read_input "kcfa2.ml";
    read_input "kcfa3.ml";
    read_input "ack.ml";
    read_input "tak.ml";
    read_input "cpstak.ml";
    read_input "loop2.ml";
    read_input "loop2'.ml";
    read_input "sat.ml";
    read_input "sat-3.ml";
    read_input "eta.ml";
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

let list_cons = "(fun x -> fun ls -> { hd = x; tl = ls })"

let list_incr =
  "let incr = fun self -> fun ls -> { hd = ls.hd + 1; tl = if hd in ls.tl then \
   self self (ls.tl) else {} } in incr incr"

let incr_cell =
  "let incr = fun self -> fun ls -> fun n -> if n = 0 then ls else self self \
   ({ hd = ls.hd + 1; tl = {} }) (n - 1) in incr incr"

(* (hd in (({ hd = 3; tl = { hd = 4; tl = {} } } | (({ hd = 3; tl = { hd = 4; tl = {} } } | (stub.tl)).tl)).tl))
   (hd in (({ hd = 4; tl = {} } | (({ hd = 3; tl = { hd = 4; tl = {} } } | (stub.tl)).tl)).tl))
   tl.hd | tl.tl.hd *)

(* TODO: count number of projs and unroll that number of time *)
let lists =
  [|
    "letassert x = (" ^ list_cons ^ " 1 ({})).hd" ^ " in x = 1";
    "letassert x = let ls = { x = 1; y = 2; z = 3 } in ls.y in x = 2";
    "letassert x = ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = {} } } \
     }.tl.hd) in x = 2";
    "letassert x = ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = {} } } \
     }.tl.hd) in x = 2";
    (* incr_cell ^ " ({ hd = 0; tl = {} }) 3"; *)
    (* list_incr ^ " ({ hd = 1; tl = {} })"; *)
    (* list_incr ^ " ({ hd = 1; tl = { hd = 2; tl = {} } })"; *)
    (* list_incr ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = {} } } })"; *)
    list_incr
    ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = {} } } } \
       })";
    (* list_incr
       ^ " ({ hd = 1; tl = { hd = 2; tl = { hd = 3; tl = { hd = 4; tl = { hd = 5; \
          tl = {} } } } } })"; *)
  |]

(* TODO: test runtime exceptions *)
(* TODO: benchmark expressiveness - runtime type error; our system is path sensitive so can serve as a type checker *)
(* performance/expressiveness table *)
(* polymorphic identity function *)
(* id = fun x -> x, appl = fun f -> fun x -> f x - 1CFA has trouble *)
(* TODO: type inferencer before Z3 *)
(* TODO: use Z3 variant type to encode records: int | bool | notafield *)
