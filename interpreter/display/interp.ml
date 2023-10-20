open Core
open Ast

exception TypeMismatch
exception Unreachable
exception Invalid_arg of string
exception Runtime_error

type d = DNil | DCons of (int * d) * d
[@@deriving compare, sexp, show { with_path = false }]

let ( => ) p d = DCons (p, d)

let rec app_d d1 d2 =
  match d1 with DNil -> d2 | DCons (p, d1') -> DCons (p, app_d d1' d2)

let hd_exn_d d = match d with DCons (p, _) -> p | DNil -> failwith "Empty D"
let rec length_d d = match d with DNil -> 0 | DCons (p, d') -> 1 + length_d d'

let rec map_d d ~f =
  match d with DNil -> DNil | DCons (p, d') -> DCons (f p, map_d d' ~f)

let filteri_d d ~f =
  let rec aux d n =
    match d with
    | DNil -> DNil
    | DCons (p, d') ->
        if f n p then DCons (p, aux d' (n + 1)) else aux d' (n + 1)
  in
  aux d 0

let rec for_all2_d d1 d2 ~f =
  match (d1, d2) with
  | DNil, DNil -> true
  | DCons (p1, d1'), DCons (p2, d2') -> f p1 p2 && for_all2_d d1' d2' ~f
  | _ -> raise (Invalid_arg "Unequal lengths")

let rec map_ls_d d ~f =
  match d with DNil -> [] | DCons (p, d') -> f p :: map_ls_d d' ~f

let fold_d d ~init ~f =
  let rec aux d acc =
    match d with DNil -> acc | DCons (p, d') -> f (aux d' acc) p
  in
  aux d init

type res =
  | DFunRes of expr * d
  | DIntRes of int
  | DBoolRes of bool
  | DPlusRes of res * res
  | DMinusRes of res * res
  | DEqRes of res * res
  | DMultRes of res * res
  | DGeRes of res * res
  | DGtRes of res * res
  | DLeRes of res * res
  | DLtRes of res * res
  | DAndRes of res * res
  | DOrRes of res * res
  | DNotRes of res
  | DRecRes of (ident * res) list
[@@deriving compare, sexp, show { with_path = false }]

let rec eval_int = function
  | DBoolRes _ | DFunRes _ | DEqRes _ | DGeRes _ | DGtRes _ | DLeRes _
  | DLtRes _ | DAndRes _ | DOrRes _ | DNotRes _ | DRecRes _ ->
      raise TypeMismatch
  | DIntRes i -> i
  | DPlusRes (r1, r2) -> eval_int r1 + eval_int r2
  | DMinusRes (r1, r2) -> eval_int r1 - eval_int r2
  | DMultRes (r1, r2) -> eval_int r1 * eval_int r2

let rec eval_bool = function
  | DIntRes _ | DFunRes _ | DPlusRes _ | DMinusRes _ | DMultRes _ | DRecRes _ ->
      raise TypeMismatch
  | DBoolRes b -> b
  | DEqRes (r1, r2) -> eval_int r1 = eval_int r2
  | DGeRes (r1, r2) -> eval_int r1 >= eval_int r2
  | DGtRes (r1, r2) -> eval_int r1 > eval_int r2
  | DLeRes (r1, r2) -> eval_int r1 <= eval_int r2
  | DLtRes (r1, r2) -> eval_int r1 < eval_int r2
  | DAndRes (r1, r2) -> eval_bool r1 && eval_bool r2
  | DOrRes (r1, r2) -> eval_bool r1 || eval_bool r2
  | DNotRes r -> not (eval_bool r)

let rec nth_exn_d d n =
  if n < 0 then raise (Invalid_arg "Negative index")
  else
    match d with
    | DNil -> raise (Invalid_arg "Index of out of bounds")
    | DCons (p, d') -> if n = 0 then p else nth_exn_d d' (n - 1)

let rec eval expr d =
  match expr with
  | DInt i -> DIntRes i
  | DBool b -> DBoolRes b
  | DFun _ -> DFunRes (expr, d)
  | DVar (Ident s, l, _) -> (
      Logs.info (fun m -> m "=== DVar (%s, %d) ===" s l);
      let l_app, dm = nth_exn_d d l in
      match Hashtbl.find_exn myexpr l_app with
      | DApp (_, em', _) ->
          Logs.info (fun m -> m "*** DVar (%s, %d) ***" s l);
          eval em' dm
      | _ -> raise Unreachable)
  | DApp (e1, e2, l) -> (
      Logs.info (fun m -> m "=== DApp ===");
      Logs.debug (fun m -> m "Evaluating %a" pp_expr expr);
      let fun_res = eval e1 d in
      match fun_res with
      | DFunRes (e_fun, d1) -> (
          let _ = eval e2 d in
          match e_fun with
          | DFun (_, e) ->
              Logs.info (fun m -> m "*** DApp ***");
              eval e ((l, d) => d1)
          | _ -> raise Unreachable)
      | _ -> raise Unreachable)
  | DPlus (e1, e2) -> DPlusRes (eval e1 d, eval e2 d)
  | DMinus (e1, e2) -> DMinusRes (eval e1 d, eval e2 d)
  | DMult (e1, e2) -> DMultRes (eval e1 d, eval e2 d)
  | DEq (e1, e2) -> DEqRes (eval e1 d, eval e2 d)
  | DGe (e1, e2) -> DGeRes (eval e1 d, eval e2 d)
  | DGt (e1, e2) -> DGtRes (eval e1 d, eval e2 d)
  | DLe (e1, e2) -> DLeRes (eval e1 d, eval e2 d)
  | DLt (e1, e2) -> DLtRes (eval e1 d, eval e2 d)
  | DAnd (e1, e2) -> DAndRes (eval e1 d, eval e2 d)
  | DOr (e1, e2) -> DOrRes (eval e1 d, eval e2 d)
  | DNot e -> DNotRes (eval e d)
  | DIf (e1, e2, e3) ->
      Logs.info (fun m -> m "=== DIf ===");
      let r1 = eval e1 d in
      if eval_bool r1 then (
        Logs.info (fun m -> m "=== DIf True ===");
        let r2 = eval e2 d in
        Logs.info (fun m -> m "*** DIf ***");
        r2)
      else (
        Logs.info (fun m -> m "=== DIf False ===");
        let r3 = eval e3 d in
        Logs.info (fun m -> m "*** DIf ***");
        r3)
  | DRec es -> DRecRes (List.map es ~f:(fun (id, e) -> (id, eval e d)))
  | DProj (e, id) -> (
      match eval e d with
      | DRecRes rs -> (
          match List.find rs ~f:(fun (id', _) -> compare_ident id id' = 0) with
          | Some (_, r) -> r
          | None -> raise Runtime_error)
      | _ -> raise Runtime_error)
  | DInsp (id, e) -> (
      match eval e d with
      | DRecRes rs ->
          DBoolRes
            (List.exists rs ~f:(fun (id', _) -> compare_ident id id' = 0))
      | _ -> raise Runtime_error)
  | DLetAssert (_, e, _) -> eval e d

let eval expr = eval expr DNil

(* TODO: compare performance of interpreters *)
