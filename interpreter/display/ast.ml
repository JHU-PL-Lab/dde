open Core

type ident = Ident of string
[@@deriving show { with_path = false }, compare, sexp, hash]

type expr =
  | DInt of int
  | DBool of bool
  | DFun of ident * expr
  | DVar of ident * int * int
  | DApp of expr * expr * int
  | DPlus of expr * expr
  | DMinus of expr * expr
  | DMult of expr * expr
  | DEq of expr * expr
  | DAnd of expr * expr
  | DOr of expr * expr
  | DGe of expr * expr
  | DGt of expr * expr
  | DLe of expr * expr
  | DLt of expr * expr
  | DNot of expr
  | DIf of expr * expr * expr
  | DRec of (ident * expr) list
  | DProj of expr * ident
  | DInsp of ident * expr
  | DLetAssert of ident * expr * expr
[@@deriving show { with_path = false }, compare, sexp, hash]

module Expr = struct
  module T = struct
    type t = expr [@@deriving compare, sexp, hash]
  end

  include T
  include Comparable.Make (T)
end

let label = ref 0

let mk_label () =
  let l = !label in
  incr label;
  l

let myexpr = Hashtbl.create (module Int)
let mylabel = Hashtbl.create (module Expr)

let mk_record l e =
  Hashtbl.add_exn myexpr ~key:l ~data:e;
  Hashtbl.add_exn mylabel ~key:e ~data:l

let get_label = Hashtbl.find_exn mylabel

let clean_up () =
  label := 0;
  Hashtbl.clear myexpr;
  Hashtbl.clear mylabel

let mk_dfun id e = DFun (id, e)
let mk_dint i = DInt i
let mk_dbool b = DBool b

let mk_dvar id =
  let l = mk_label () in
  let e = DVar (id, -1, l) in
  mk_record l e;
  e

let mk_dapp e1 e2 =
  let l = mk_label () in
  let e = DApp (e1, e2, l) in
  mk_record l e;
  e

let mk_dplus e1 e2 = DPlus (e1, e2)
let mk_dminus e1 e2 = DMinus (e1, e2)
let mk_dmult e1 e2 = DMult (e1, e2)
let mk_deq e1 e2 = DEq (e1, e2)
let mk_dge e1 e2 = DGe (e1, e2)
let mk_dgt e1 e2 = DGt (e1, e2)
let mk_dle e1 e2 = DLe (e1, e2)
let mk_dlt e1 e2 = DLt (e1, e2)
let mk_dand e1 e2 = DAnd (e1, e2)
let mk_dor e1 e2 = DOr (e1, e2)
let mk_dnot e = DNot e
let mk_dif e1 e2 e3 = DIf (e1, e2, e3)

let mk_dlet id e1 e2 =
  let l = mk_label () in
  let e = DApp (DFun (id, e2), e1, l) in
  mk_record l e;
  e

let mk_drec es = DRec es
let mk_dproj e id = DProj (e, id)
let mk_dinsp id e = DInsp (id, e)
let mk_dletassert id e1 e2 = DLetAssert (id, e1, e2)

let rec assign_depth ?(d = 0) ?(m = String.Map.empty) e =
  match e with
  | DInt _ | DBool _ -> e
  | DVar ((Ident x as id), _, l) -> DVar (id, d - Map.find_exn m x, l)
  | DFun ((Ident x as id), e) ->
      let d = d + 1 in
      DFun
        (id, assign_depth e ~d ~m:(Map.add_exn (Map.remove m x) ~key:x ~data:d))
  | DApp (e1, e2, l) ->
      let e' = DApp (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m, l) in
      Hashtbl.remove myexpr l;
      Hashtbl.add_exn myexpr ~key:l ~data:e';
      Hashtbl.remove mylabel e;
      Hashtbl.add_exn mylabel ~key:e' ~data:l;
      e'
  | DPlus (e1, e2) -> DPlus (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DMinus (e1, e2) -> DMinus (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DMult (e1, e2) -> DMinus (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DEq (e1, e2) -> DEq (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DGe (e1, e2) -> DGe (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DGt (e1, e2) -> DGt (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DLe (e1, e2) -> DLe (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DLt (e1, e2) -> DLt (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DAnd (e1, e2) -> DAnd (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DOr (e1, e2) -> DOr (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m)
  | DNot e1 -> DNot (assign_depth e ~d ~m)
  | DIf (e1, e2, e3) ->
      DIf (assign_depth e1 ~d ~m, assign_depth e2 ~d ~m, assign_depth e3 ~d ~m)
  | DRec es -> DRec (List.map es ~f:(fun (id, e) -> (id, assign_depth e ~d ~m)))
  | DProj (e, id) -> DProj (assign_depth e ~d ~m, id)
  | DInsp (id, e) -> DInsp (id, assign_depth e ~d ~m)
  | DLetAssert (id, e1, e2) -> DLetAssert (id, assign_depth e1 ~d ~m, e2)
