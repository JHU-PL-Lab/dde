open Ddeast

exception TypeMismatch

let rec transform_let e =
  match e with
  | Let (ident, e1, e2, let_label) ->
      let func_label = get_next_label () in
      let e2' = transform_let e2 in
      let func = Function (ident, e2', func_label) in
      add_expr func_label func;
      let e1' = transform_let e1 in
      let appl = Appl (func, e1', let_label) in
      add_expr let_label appl;
      appl
  | Function (ident, e, func_label) ->
      let e' = transform_let e in
      let func = Function (ident, e', func_label) in
      add_expr func_label func;
      func
  | Appl (e1, e2, appl_label) ->
      let e1' = transform_let e1 in
      let e2' = transform_let e2 in
      let appl = Appl (e1', e2', appl_label) in
      add_expr appl_label appl;
      appl
  | _ -> e

let get_label e =
  match e with
  (* TODO: mutually recursive types *)
  | Int (_, label)
  | Function (_, _, label)
  | Bool (_, label)
  | Appl (_, _, label)
  | Var (_, label)
  | Plus (_, _, label)
  | Minus (_, _, label)
  | Equal (_, _, label)
  | And (_, _, label)
  | Or (_, _, label)
  | Not (_, label)
  | If (_, _, _, label)
  | Let (_, _, _, label) ->
      label

let memo_cache = Hashtbl.create 1000

(* can't do memoization like this in OCaml/Haskell; better laziness  *)
(* laziness + memoization *)
let rec eval_helper ?(is_lazy = false) e sigma =
  match Hashtbl.find_opt memo_cache (e, sigma) with
  | Some res -> res
  | None ->
      let eval_res =
        match e with
        (* Value *)
        | Function (_, _, label) -> (label, sigma)
        | Int (_, label) -> (label, None)
        | Bool (_, label) -> (label, None)
        (* Application *)
        | Appl (e1, _, appl_label) -> (
            if is_lazy then (appl_label, None)
            else
              let fun_label, sigma' = eval_helper e1 sigma in
              match get_expr fun_label with
              | Function (_, e, _) ->
                  eval_helper e (Some (appl_label :: Option.get sigma)) ~is_lazy
              | _ -> failwith "appl")
        | Var (Ident x, var_label) -> (
            match get_outer_scope var_label |> get_expr with
            | Function (Ident x', _, _) -> (
                let sigma = Option.get sigma in
                if x = x' then
                  (* Var Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (_, e2, _) ->
                      eval_helper e2 (Some (List.tl sigma)) ~is_lazy
                  | _ -> failwith "local"
                else
                  (* Var Non-Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (e1, _, _) ->
                      let fun_label, sigma' =
                        eval_helper e1 (Some (List.tl sigma))
                      in
                      eval_helper (Var (Ident x, fun_label)) sigma' ~is_lazy
                  | _ -> failwith "non-local")
            | _ -> failwith "var")
        | Plus (e1, e2, label) | Minus (e1, e2, label) | Equal (e1, e2, label)
          -> (
            if is_lazy then (label, None)
            else
              let l1, _ = eval_helper e1 sigma in
              let l2, _ = eval_helper e2 sigma in
              let e1 = get_expr l1 in
              let e2 = get_expr l2 in
              match (e1, e2) with
              | Int (i1, _), Int (i2, _) -> (
                  let res_label = get_next_label () in
                  match e with
                  | Plus (_, _, _) ->
                      let res_exp = Int (i1 + i2, res_label) in
                      add_expr res_label res_exp;
                      (res_label, None)
                  | Minus (_, _, _) ->
                      let res_exp = Int (i1 - i2, res_label) in
                      add_expr res_label res_exp;
                      (res_label, None)
                  | Equal (_, _, _) ->
                      let res_exp = Bool (i1 = i2, res_label) in
                      add_expr res_label res_exp;
                      (res_label, None)
                  | _ -> failwith "unreachable")
              | _ -> raise TypeMismatch)
        | And (e1, e2, label) | Or (e1, e2, label) -> (
            if is_lazy then (label, None)
            else
              let l1, _ = eval_helper e1 sigma in
              let l2, _ = eval_helper e2 sigma in
              let e1 = get_expr l1 in
              let e2 = get_expr l2 in
              match (e1, e2) with
              | Bool (b1, _), Bool (b2, _) -> (
                  let res_label = get_next_label () in
                  match e with
                  | And (_, _, _) ->
                      let res_exp = Bool (b1 && b2, res_label) in
                      add_expr res_label res_exp;
                      (res_label, None)
                  | Or (_, _, _) ->
                      let res_exp = Bool (b1 || b2, res_label) in
                      add_expr res_label res_exp;
                      (res_label, None)
                  | _ -> failwith "unreachable")
              | _ -> raise TypeMismatch)
        | Not (e, label) -> (
            if is_lazy then (label, None)
            else
              let l, _ = eval_helper e sigma in
              let e = get_expr l in
              match e with
              | Bool (b, _) ->
                  let res_label = get_next_label () in
                  let res_exp = Bool (not b, res_label) in
                  add_expr res_label res_exp;
                  (res_label, None)
              | _ -> failwith "unreachable")
        | If (e1, e2, e3, label) -> (
            if is_lazy then (label, None)
            else
              let cond_label, _ = eval_helper e1 sigma in
              match get_expr cond_label with
              | Bool (b, _) ->
                  if b then eval_helper e2 sigma ~is_lazy
                  else eval_helper e3 sigma ~is_lazy
              | _ -> raise TypeMismatch)
        | Let (_, _, _, _) -> failwith "unreachable"
      in
      let () = Hashtbl.replace memo_cache (e, sigma) eval_res in
      eval_res

module StringSet = Set.Make (String)

let rec label_to_expr target_label e sigma seen =
  match e with
  | Int (_, _) -> e
  | Bool (_, _) -> e
  | Function (Ident x, e, label) ->
      Function
        ( Ident x,
          label_to_expr target_label e sigma (StringSet.add x seen),
          label )
  | Var (Ident x, var_label) as e ->
      if StringSet.mem x seen then e
      else
        eval_helper (Var (Ident x, target_label)) sigma ~is_lazy:true
        |> fst |> get_expr
  | Appl (e1, e2, label) ->
      Appl
        ( label_to_expr target_label e1 sigma seen,
          label_to_expr target_label e2 sigma seen,
          label )
  | Plus (e1, e2, label) | Minus (e1, e2, label) | Equal (e1, e2, label) -> (
      let e1 = label_to_expr target_label e1 sigma seen in
      let e2 = label_to_expr target_label e2 sigma seen in
      match e with
      | Plus (_, _, _) -> Plus (e1, e2, label)
      | Minus (_, _, _) -> Minus (e1, e2, label)
      | Equal (_, _, _) -> Equal (e1, e2, label)
      | _ -> failwith "unreachable")
  | And (e1, e2, label) | Or (e1, e2, label) -> (
      let e1 = label_to_expr target_label e1 sigma seen in
      let e2 = label_to_expr target_label e2 sigma seen in
      match e with
      | And (_, _, _) -> And (e1, e2, label)
      | Or (_, _, _) -> Or (e1, e2, label)
      | _ -> failwith "unreachable")
  | Not (e, label) -> Not (label_to_expr target_label e sigma seen, label)
  | If (e1, e2, e3, label) ->
      If
        ( label_to_expr target_label e1 sigma seen,
          label_to_expr target_label e2 sigma seen,
          label_to_expr target_label e3 sigma seen,
          label )
  | Let (_, _, _, _) -> failwith "unreachable"

let eval is_debug_mode e =
  let e = transform_let e in
  let () = fill_my_fun e None in
  let label, sigma = eval_helper e (Some []) in

  if is_debug_mode then (
    print_endline "****** Label Table ******";
    print_my_expr my_expr;
    print_endline "****** Label Table ******\n";
    print_endline "****** MyFun Table ******";
    print_my_fun my_fun;
    print_endline "****** MyFun Table ******\n");

  let e = label_to_expr label (get_expr label) sigma StringSet.empty in
  Hashtbl.reset my_expr;
  Hashtbl.reset my_fun;
  e
