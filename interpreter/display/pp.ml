open Core
open Ast
open Interp

let ff = Format.fprintf

let paren_if cond pp fmt e =
  if cond e then ff fmt "(%a)" pp e else ff fmt "%a" pp e

let is_compound_expr = function DVar _ -> false | _ -> true

let rec pp_expr fmt = function
  | DInt i -> ff fmt "%d" i
  | DBool b -> ff fmt "%b" b
  | DVar (Ident x, l, _) -> ff fmt "%s@%d" x l
  (* | DVar (Ident x, _, _) -> ff fmt "%s" x *)
  | DFun (Ident x, e) -> ff fmt "@[<hv>fun %s ->@;<1 4>%a@]" x pp_expr e
  | DApp (e1, e2, _) ->
      let is_compound_exprL = function
        | DApp _ -> false
        | other -> is_compound_expr other
      in
      ff fmt "%a %a"
        (paren_if is_compound_exprL pp_expr)
        e1
        (paren_if is_compound_expr pp_expr)
        e2
  | DIf (e1, e2, e3) ->
      ff fmt "@[<hv>if %a then@;<1 4>%a@;<1 0>else@;<1 4>%a@]" pp_expr e1
        pp_expr e2 pp_expr e3
  | DPlus (e1, e2) -> ff fmt "%a + %a" pp_expr e1 pp_expr e2
  | DMinus (e1, e2) -> ff fmt "%a - %a" pp_expr e1 pp_expr e2
  | DEq (e1, e2) -> ff fmt "%a = %a" pp_expr e1 pp_expr e2
  | DGe (e1, e2) -> ff fmt "%a >= %a" pp_expr e1 pp_expr e2
  | DGt (e1, e2) -> ff fmt "%a > %a" pp_expr e1 pp_expr e2
  | DLe (e1, e2) -> ff fmt "%a <= %a" pp_expr e1 pp_expr e2
  | DLt (e1, e2) -> ff fmt "%a < %a" pp_expr e1 pp_expr e2
  | DAnd (e1, e2) -> ff fmt "%a && %a" pp_expr e1 pp_expr e2
  | DOr (e1, e2) -> ff fmt "%a || %a" pp_expr e1 pp_expr e2
  | DRec es ->
      if List.length es = 0 then ff fmt "{}" else ff fmt "{ %a }" pp_rec es
  | DProj (e, Ident x) -> ff fmt "%a.%s" pp_expr e x
  | DInsp (Ident x, e) -> ff fmt "%s in %a" x pp_expr e
  | e ->
      Format.printf "%s\n" (show_expr e);
      failwith "unimplemented"

and pp_rec fmt = function
  | [] -> ()
  | [ (Ident x, e) ] -> ff fmt "%s = %a" x pp_expr e
  | (Ident x, e) :: es -> ff fmt "%s = %a; %a" x pp_expr e pp_rec es

let rec pp_res fmt = function
  | DIntRes i -> ff fmt "%d" i
  | DBoolRes b -> ff fmt "%b" b
  | DFunRes (e, _) -> ff fmt "%a" pp_expr e
  | DPlusRes (r1, r2) -> ff fmt "%a + %a" pp_res r1 pp_res r2
  | DMinusRes (r1, r2) -> ff fmt "%a - %a" pp_res r1 pp_res r2
  | DMultRes (r1, r2) -> ff fmt "%a * %a" pp_res r1 pp_res r2
  | DEqRes (r1, r2) -> ff fmt "%a = %a" pp_res r1 pp_res r2
  | DGeRes (r1, r2) -> ff fmt "%a >= %a" pp_res r1 pp_res r2
  | DGtRes (r1, r2) -> ff fmt "%a > %a" pp_res r1 pp_res r2
  | DLeRes (r1, r2) -> ff fmt "%a <= %a" pp_res r1 pp_res r2
  | DLtRes (r1, r2) -> ff fmt "%a < %a" pp_res r1 pp_res r2
  | DAndRes (r1, r2) -> ff fmt "%a && %a" pp_res r1 pp_res r2
  | DOrRes (r1, r2) -> ff fmt "%a || %a" pp_res r1 pp_res r2
  | DNotRes r -> ff fmt "not %a" pp_res r
  | DRecRes rs -> ff fmt "{ %a }" pp_rec rs

and pp_rec fmt = function
  | [] -> ff fmt ""
  | [ (Ident x, r) ] -> ff fmt "%s = %a" x pp_res r
  | (Ident x, r) :: rs -> ff fmt "%s = %a; %a" x pp_res r pp_rec rs

let rec show_d_pp d =
  d
  |> map_ls_d ~f:(fun (l, d) -> Format.asprintf "%d^%s" l (show_d_pp d))
  |> String.concat ~sep:"; " |> Format.sprintf "[%s]"

let rec show_d_lens d =
  d
  |> map_ls_d ~f:(fun (_, d) ->
         Format.asprintf "%d^%s" (length_d d) (show_d_lens d))
  |> String.concat ~sep:"; " |> Format.sprintf "[%s]"

let pp_d fmt d =
  let rec aux fmt = function
    | DNil -> ()
    | DCons ((l, d), DNil) ->
        if length_d d = 0 then ff fmt "%d" l else ff fmt "%d^[ %a ]" l aux d
    | DCons ((l, d), d') ->
        if length_d d = 0 then ff fmt "%d; %a" l aux d'
        else ff fmt "%d^[ %a ]; %a" l aux d aux d'
  in
  if length_d d = 0 then ff fmt "[]" else ff fmt "[ %a ]" aux d

let pp_myexpr fmt myexpr =
  myexpr
  |> Hashtbl.map ~f:(Format.asprintf "%a" pp_expr)
  |> Hashtbl.to_alist
  |> List.sort ~compare:(fun (l1, _) (l2, _) -> Int.ascending l1 l2)
  |> List.map ~f:(fun (l, s) -> Format.sprintf "%d -> %s" l s)
  |> String.concat ~sep:"\n" |> ff fmt "%s"
