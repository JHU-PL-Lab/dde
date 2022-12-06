open Ddeast

exception TypeMismatch
exception Unreachable

let rec transform_let e =
  match e with
  | Let (ident, e1, e2), let_label ->
      let func_label = get_next_label () in
      let e2' = transform_let e2 in
      let func = (Function (ident, e2'), func_label) in
      add_expr func_label func;
      let e1' = transform_let e1 in
      let appl = (Appl (func, e1'), let_label) in
      add_expr let_label appl;
      appl
  | Function (ident, e), func_label ->
      let e' = transform_let e in
      let func = (Function (ident, e'), func_label) in
      add_expr func_label func;
      func
  | Appl (e1, e2), appl_label ->
      let e1' = transform_let e1 in
      let e2' = transform_let e2 in
      let appl = (Appl (e1', e2'), appl_label) in
      add_expr appl_label appl;
      appl
  | _ -> e

let memo_cache = Hashtbl.create 1000

(* can't do memoization like this in OCaml/Haskell; better laziness  *)
(* laziness + memoization *)
let rec eval_helper ?(is_lazy = false) le sigma =
  match Hashtbl.find_opt memo_cache (le, sigma) with
  | Some res -> res
  | None ->
      let e, label = le in
      let eval_res =
        match e with
        (* Value *)
        | Function (_, _) -> (le, sigma)
        | Int _ -> (le, None)
        | Bool _ -> (le, None)
        (* Application *)
        | Appl (e1, _) -> (
            if is_lazy then (le, None)
            else
              let fun_le = eval_helper e1 sigma |> fst |> fst in
              match fun_le with
              | Function (_, e') ->
                  eval_helper e' (Some (label :: Option.get sigma)) ~is_lazy
              | _ -> raise Unreachable [@coverage off])
        | Var (Ident x) -> (
            match get_outer_scope label |> fst with
            | Function (Ident x', _) -> (
                let sigma = Option.get sigma in
                if x = x' then
                  (* Var Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (_, e2), _ ->
                      eval_helper e2 (Some (List.tl sigma)) ~is_lazy
                  | _ -> raise Unreachable [@coverage off]
                else
                  (* Var Non-Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (e1, _), _ ->
                      let (_, fun_label), sigma' =
                        eval_helper e1 (Some (List.tl sigma))
                      in
                      eval_helper (Var (Ident x), fun_label) sigma' ~is_lazy
                  | _ -> raise Unreachable [@coverage off])
            | _ -> raise Unreachable [@coverage off])
        | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) -> (
            if is_lazy then (le, None)
            else
              let e1 = eval_helper e1 sigma |> fst |> fst in
              let e2 = eval_helper e2 sigma |> fst |> fst in
              match (e1, e2) with
              | Int i1, Int i2 -> (
                  let res_label = get_next_label () in
                  match e with
                  | Plus (_, _) ->
                      let res_exp = (Int (i1 + i2), res_label) in
                      add_expr res_label res_exp;
                      (res_exp, None)
                  | Minus (_, _) ->
                      let res_exp = (Int (i1 - i2), res_label) in
                      add_expr res_label res_exp;
                      (res_exp, None)
                  | Equal (_, _) ->
                      let res_exp = (Bool (i1 = i2), res_label) in
                      add_expr res_label res_exp;
                      (res_exp, None)
                  | _ -> raise Unreachable [@coverage off])
              | _ -> raise TypeMismatch)
        | And (e1, e2) | Or (e1, e2) -> (
            if is_lazy then (le, None)
            else
              let e1 = eval_helper e1 sigma |> fst |> fst in
              let e2 = eval_helper e2 sigma |> fst |> fst in
              match (e1, e2) with
              | Bool b1, Bool b2 -> (
                  let res_label = get_next_label () in
                  match e with
                  | And (_, _) ->
                      let res_exp = (Bool (b1 && b2), res_label) in
                      add_expr res_label res_exp;
                      (res_exp, None)
                  | Or (_, _) ->
                      let res_exp = (Bool (b1 || b2), res_label) in
                      add_expr res_label res_exp;
                      (res_exp, None)
                  | _ -> raise Unreachable [@coverage off])
              | _ -> raise TypeMismatch)
        | Not e -> (
            if is_lazy then (le, None)
            else
              let e = eval_helper e sigma |> fst |> fst in
              match e with
              | Bool b ->
                  let res_label = get_next_label () in
                  let res_exp = (Bool (not b), res_label) in
                  add_expr res_label res_exp;
                  (res_exp, None)
              | _ -> raise TypeMismatch)
        | If (e1, e2, e3) -> (
            if is_lazy then (le, None)
            else
              let cond_expr = eval_helper e1 sigma |> fst |> fst in
              match cond_expr with
              | Bool b ->
                  if b then eval_helper e2 sigma ~is_lazy
                  else eval_helper e3 sigma ~is_lazy
              | _ -> raise TypeMismatch)
        | Let (_, _, _) -> raise Unreachable [@coverage off]
      in
      let () = Hashtbl.replace memo_cache (le, sigma) eval_res in
      eval_res

module StringSet = Set.Make (String)

let rec label_to_expr target_label target sigma seen =
  let expr, label = target in
  match expr with
  | Int _ -> target
  | Bool _ -> target
  | Function (Ident x, e) ->
      ( Function
          (Ident x, label_to_expr target_label e sigma (StringSet.add x seen)),
        label )
  | Var (Ident x) ->
      if StringSet.mem x seen then target (* only substitute free variables *)
      else eval_helper (expr, target_label) sigma ~is_lazy:true |> fst
  | Appl (e1, e2) ->
      ( Appl
          ( label_to_expr target_label e1 sigma seen,
            label_to_expr target_label e2 sigma seen ),
        label )
  | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) | And (e1, e2) | Or (e1, e2)
    -> (
      let e1 = label_to_expr target_label e1 sigma seen in
      let e2 = label_to_expr target_label e2 sigma seen in
      match expr with
      | Plus (_, _) -> (Plus (e1, e2), label)
      | Minus (_, _) -> (Minus (e1, e2), label)
      | Equal (_, _) -> (Equal (e1, e2), label)
      | And (_, _) -> (And (e1, e2), label)
      | Or (_, _) -> (Or (e1, e2), label)
      | _ -> raise Unreachable [@coverage off])
  | Not e -> (Not (label_to_expr target_label e sigma seen), label)
  | If (e1, e2, e3) ->
      ( If
          ( label_to_expr target_label e1 sigma seen,
            label_to_expr target_label e2 sigma seen,
            label_to_expr target_label e3 sigma seen ),
        label )
  | Let (_, _, _) -> raise Unreachable [@coverage off]

let eval is_debug_mode e =
  let e = transform_let e in
  let () = fill_my_fun e None in
  let target, sigma = eval_helper e (Some []) in
  let _, target_label = target in

  if is_debug_mode then (
    (print_endline "****** Label Table ******";
     print_my_expr my_expr;
     print_endline "****** Label Table ******\n";
     print_endline "****** MyFun Table ******";
     print_my_fun my_fun;
     print_endline "****** MyFun Table ******\n")
    [@coverage off]);

  let e = label_to_expr target_label target sigma StringSet.empty in
  Hashtbl.reset my_expr;
  Hashtbl.reset my_fun;
  e
