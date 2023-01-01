open Ddeast

exception TypeMismatch
exception Unreachable

let rec transform_let e =
  match e with
  | Value value -> (
      match value with
      | Function (ident, e, l) ->
          let e' = transform_let e in
          let f = Value (Function (ident, e', l)) in
          add_expr l f;
          f
      | _ -> e)
  | Let (ident, e1, e2, let_l) ->
      let fun_l = get_next_label () in
      let e2' = transform_let e2 in
      let f = Value (Function (ident, e2', fun_l)) in
      add_expr fun_l f;
      let e1' = transform_let e1 in
      let appl = Appl (f, e1', let_l) in
      add_expr let_l appl;
      appl
  | Appl (e1, e2, l) ->
      let e1' = transform_let e1 in
      let e2' = transform_let e2 in
      let appl = Appl (e1', e2', l) in
      add_expr l appl;
      appl
  | _ -> e

type op_result_value =
  | Plus of result_value * result_value
  | Minus of result_value * result_value
  | Equal of result_value * result_value
  | And of result_value * result_value
  | Or of result_value * result_value
  | Not of result_value

and result_value =
  | FunctionResult of { f : value; l : int; sigma : int list }
  | IntResult of int
  | BoolResult of bool
  | OpResult of op_result_value
[@@deriving show { with_path = false }]

let rec eval_int (r : result_value) : int =
  match r with
  | FunctionResult _ | BoolResult _ -> raise TypeMismatch
  | IntResult i -> i
  | OpResult op_r -> (
      match op_r with
      | Plus (r1, r2) -> eval_int r1 + eval_int r2
      | Minus (r1, r2) -> eval_int r1 - eval_int r2
      | Equal (r1, r2) -> raise TypeMismatch
      | And (r1, r2) -> raise TypeMismatch
      | Or (r1, r2) -> raise TypeMismatch
      | Not r -> raise TypeMismatch)

let rec eval_bool (r : result_value) : bool =
  match r with
  | FunctionResult _ | IntResult _ -> raise TypeMismatch
  | BoolResult b -> b
  | OpResult op_r -> (
      match op_r with
      | Plus (r1, r2) -> raise TypeMismatch
      | Minus (r1, r2) -> raise TypeMismatch
      | Equal (r1, r2) -> eval_int r1 = eval_int r2
      | And (r1, r2) -> eval_bool r1 && eval_bool r2
      | Or (r1, r2) -> eval_bool r1 || eval_bool r2
      | Not r -> not (eval_bool r))

let memo_cache = Hashtbl.create 1000

(* can't do memoization like this in OCaml/Haskell; better laziness  *)
(* laziness + memoization *)
let rec eval_helper (e : expr) (sigma : int list) : result_value =
  match Hashtbl.find_opt memo_cache (e, sigma) with
  | Some res -> res
  | None ->
      let eval_res =
        match e with
        (* Value *)
        | Value v -> (
            match v with
            | Function (ident, le', l) -> FunctionResult { f = v; l; sigma }
            | Int i -> IntResult i
            | Bool b -> BoolResult b)
        (* Application *)
        | Appl (e1, _, app_l) -> (
            match eval_helper e1 sigma with
            | FunctionResult { f = Function (_, e, _); l; sigma = sigma' } ->
                eval_helper e (app_l :: sigma)
            | _ -> raise Unreachable [@coverage off])
        | Var (Ident x, l) -> (
            match get_outer_scope l with
            | Value (Function (Ident x', _, _)) -> (
                if x = x' then
                  (* Var Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (_, e2, _) -> eval_helper e2 (List.tl sigma)
                  | _ -> raise Unreachable [@coverage off]
                else
                  (* Var Non-Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (e1, _, _) -> (
                      match eval_helper e1 (List.tl sigma) with
                      | FunctionResult { f; l = l1; sigma = sigma1 } ->
                          eval_helper (Var (Ident x, l1)) sigma1
                      | _ -> raise Unreachable [@coverage off])
                  | _ -> raise Unreachable [@coverage off])
            | _ -> raise Unreachable [@coverage off])
        | Plus (e1, e2, _) ->
            let r1 = eval_helper e1 sigma in
            let r2 = eval_helper e2 sigma in
            OpResult (Plus (r1, r2))
        | Minus (e1, e2, _) ->
            let r1 = eval_helper e1 sigma in
            let r2 = eval_helper e2 sigma in
            OpResult (Minus (r1, r2))
        | Equal (e1, e2, _) ->
            let r1 = eval_helper e1 sigma in
            let r2 = eval_helper e2 sigma in
            OpResult (Equal (r1, r2))
        | And (e1, e2, _) ->
            let r1 = eval_helper e1 sigma in
            let r2 = eval_helper e2 sigma in
            OpResult (And (r1, r2))
        | Or (e1, e2, _) ->
            let r1 = eval_helper e1 sigma in
            let r2 = eval_helper e2 sigma in
            OpResult (Or (r1, r2))
        | Not (e, _) -> OpResult (Not (eval_helper e sigma))
        | If (e1, e2, e3, _) ->
            let r = eval_helper e1 sigma in
            if eval_bool r then eval_helper e2 sigma else eval_helper e3 sigma
        | Let (_, _, _, _) -> raise Unreachable [@coverage off]
      in
      let () = Hashtbl.replace memo_cache (e, sigma) eval_res in
      eval_res

module StringSet = Set.Make (String)

let rec subst_free_vars (e : expr) (target_l : int) (sigma : int list)
    (seen : StringSet.t) =
  match e with
  | Value v -> (
      match v with
      | Int _ -> e
      | Bool _ -> e
      | Function (Ident x, e', l) ->
          Value
            (Function
               ( Ident x,
                 subst_free_vars e' target_l sigma (StringSet.add x seen),
                 l )))
  | Var (Ident x, _) -> (
      if StringSet.mem x seen then e (* only substitute free variables *)
      else
        let r = eval_helper (Var (Ident x, target_l)) sigma in
        match eval_result_value r with
        | IntResult i -> Value (Int i)
        | BoolResult b -> Value (Bool b)
        | FunctionResult { f; _ } -> Value f
        | OpResult _ -> raise Unreachable [@coverage off])
  | Appl (e1, e2, l) ->
      Appl
        ( subst_free_vars e1 target_l sigma seen,
          subst_free_vars e2 target_l sigma seen,
          l )
  | Plus (e1, e2, l)
  | Minus (e1, e2, l)
  | Equal (e1, e2, l)
  | And (e1, e2, l)
  | Or (e1, e2, l) -> (
      let e1 = subst_free_vars e1 target_l sigma seen in
      let e2 = subst_free_vars e2 target_l sigma seen in
      match e with
      | Plus (_, _, _) -> Plus (e1, e2, l)
      | Minus (_, _, _) -> Minus (e1, e2, l)
      | Equal (_, _, _) -> Equal (e1, e2, l)
      | And (_, _, _) -> And (e1, e2, l)
      | Or (_, _, _) -> Or (e1, e2, l)
      | _ -> raise Unreachable [@coverage off])
  | Not (e, l) -> Not (subst_free_vars e target_l sigma seen, l)
  | If (e1, e2, e3, l) ->
      If
        ( subst_free_vars e1 target_l sigma seen,
          subst_free_vars e2 target_l sigma seen,
          subst_free_vars e3 target_l sigma seen,
          l )
  | Let (_, _, _, _) -> raise Unreachable [@coverage off]

and eval_result_value (r : result_value) : result_value =
  match r with
  | IntResult i -> r
  | BoolResult b -> r
  | FunctionResult { f; l; sigma } -> (
      match f with
      | Function (Ident x, e, l) ->
          FunctionResult
            {
              f =
                Function
                  (Ident x, subst_free_vars e l sigma (StringSet.singleton x), l);
              l;
              sigma;
            }
      | _ -> raise Unreachable [@coverage off])
  | OpResult op -> (
      match op with
      | Plus (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> IntResult (i1 + i2)
          | _ -> raise TypeMismatch [@coverage off])
      | Minus (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> IntResult (i1 - i2)
          | _ -> raise TypeMismatch [@coverage off])
      | Equal (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> BoolResult (i1 = i2)
          | _ -> raise TypeMismatch [@coverage off])
      | And (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | BoolResult b1, BoolResult b2 -> BoolResult (b1 && b2)
          | _ -> raise TypeMismatch [@coverage off])
      | Or (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | BoolResult b1, BoolResult b2 -> BoolResult (b1 || b2)
          | _ -> raise TypeMismatch [@coverage off])
      | Not r -> (
          let v = eval_result_value r in
          match v with
          | BoolResult b -> BoolResult (not b)
          | _ -> raise TypeMismatch [@coverage off]))

let eval is_debug_mode e =
  let e = transform_let e in
  fill_my_fun e None;
  let r = eval_helper e [] in

  if is_debug_mode then (
    (print_endline "****** Label Table ******";
     print_my_expr my_expr;
     print_endline "****** Label Table ******\n";
     print_endline "****** MyFun Table ******";
     print_my_fun my_fun;
     print_endline "****** MyFun Table ******\n")
    [@coverage off]);

  let v = eval_result_value r in
  Hashtbl.reset my_expr;
  Hashtbl.reset my_fun;
  v
