open Ast

exception TypeMismatch
exception Unreachable

type op_result_value =
  | PlusOp of result_value * result_value
  | MinusOp of result_value * result_value
  | EqualOp of result_value * result_value
  | AndOp of result_value * result_value
  | OrOp of result_value * result_value
  | NotOp of result_value

and result_value =
  | FunResult of { f : expr; l : int; sigma : int list }
  | IntResult of int
  | BoolResult of bool
  | OpResult of op_result_value
[@@deriving show { with_path = false }]

let rec eval_int (r : result_value) : int =
  match r with
  | FunResult _ | BoolResult _ -> raise TypeMismatch
  | IntResult i -> i
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2) -> eval_int r1 + eval_int r2
      | MinusOp (r1, r2) -> eval_int r1 - eval_int r2
      | EqualOp (r1, r2) -> raise TypeMismatch
      | AndOp (r1, r2) -> raise TypeMismatch
      | OrOp (r1, r2) -> raise TypeMismatch
      | NotOp r -> raise TypeMismatch)

let rec eval_bool (r : result_value) : bool =
  match r with
  | FunResult _ | IntResult _ -> raise TypeMismatch
  | BoolResult b -> b
  | OpResult op_r -> (
      match op_r with
      | PlusOp (r1, r2) -> raise TypeMismatch
      | MinusOp (r1, r2) -> raise TypeMismatch
      | EqualOp (r1, r2) -> eval_int r1 = eval_int r2
      | AndOp (r1, r2) -> eval_bool r1 && eval_bool r2
      | OrOp (r1, r2) -> eval_bool r1 || eval_bool r2
      | NotOp r -> not (eval_bool r))

let memo_cache = Hashtbl.create 1000

(* can't do memoization like this in OCaml/Haskell; better laziness  *)
(* laziness + memoization *)
let rec eval_aux (e : expr) (sigma : int list) : result_value =
  match Hashtbl.find_opt memo_cache (e, sigma) with
  | Some res -> res
  | None ->
      let eval_res =
        match e with
        (* Value *)
        | Function (ident, le', l) -> FunResult { f = e; l; sigma }
        | Int i -> IntResult i
        | Bool b -> BoolResult b
        (* Application *)
        | Appl (e1, _, app_l) -> (
            match eval_aux e1 sigma with
            | FunResult { f = Function (_, e, _); l; sigma = sigma' } ->
                eval_aux e (app_l :: sigma)
            | _ -> raise Unreachable [@coverage off])
        | Var (Ident x, l) -> (
            match get_outer_scope l with
            | Function (Ident x', _, _) -> (
                if x = x' then
                  (* Var Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (_, e2, _) -> eval_aux e2 (List.tl sigma)
                  | _ -> raise Unreachable [@coverage off]
                else
                  (* Var Non-Local *)
                  match get_expr (List.hd sigma) with
                  | Appl (e1, _, _) -> (
                      match eval_aux e1 (List.tl sigma) with
                      | FunResult { f; l = l1; sigma = sigma1 } ->
                          eval_aux (Var (Ident x, l1)) sigma1
                      | _ -> raise Unreachable [@coverage off])
                  | _ -> raise Unreachable [@coverage off])
            | _ -> raise Unreachable [@coverage off])
        | Plus (e1, e2) ->
            let r1 = eval_aux e1 sigma in
            let r2 = eval_aux e2 sigma in
            OpResult (PlusOp (r1, r2))
        | Minus (e1, e2) ->
            let r1 = eval_aux e1 sigma in
            let r2 = eval_aux e2 sigma in
            OpResult (MinusOp (r1, r2))
        | Equal (e1, e2) ->
            let r1 = eval_aux e1 sigma in
            let r2 = eval_aux e2 sigma in
            OpResult (EqualOp (r1, r2))
        | And (e1, e2) ->
            let r1 = eval_aux e1 sigma in
            let r2 = eval_aux e2 sigma in
            OpResult (AndOp (r1, r2))
        | Or (e1, e2) ->
            let r1 = eval_aux e1 sigma in
            let r2 = eval_aux e2 sigma in
            OpResult (OrOp (r1, r2))
        | Not e -> OpResult (NotOp (eval_aux e sigma))
        | If (e1, e2, e3, _) ->
            let r = eval_aux e1 sigma in
            if eval_bool r then eval_aux e2 sigma else eval_aux e3 sigma
        | Let (_, _, _, _) -> raise Unreachable [@coverage off]
      in
      let () = Hashtbl.replace memo_cache (e, sigma) eval_res in
      eval_res

module StringSet = Set.Make (String)

let rec subst_free_vars (e : expr) (target_l : int) (sigma : int list)
    (seen : StringSet.t) =
  match e with
  | Int _ -> e
  | Bool _ -> e
  | Function (Ident x, e', l) ->
      Function
        (Ident x, subst_free_vars e' target_l sigma (StringSet.add x seen), l)
  | Var (Ident x, _) -> (
      if StringSet.mem x seen then e (* only substitute free variables *)
      else
        let r = eval_aux (Var (Ident x, target_l)) sigma in
        match eval_result_value r with
        | IntResult i -> Int i
        | BoolResult b -> Bool b
        | FunResult { f; _ } -> f
        | OpResult _ -> raise Unreachable [@coverage off])
  | Appl (e1, e2, l) ->
      Appl
        ( subst_free_vars e1 target_l sigma seen,
          subst_free_vars e2 target_l sigma seen,
          l )
  | Plus (e1, e2) | Minus (e1, e2) | Equal (e1, e2) | And (e1, e2) | Or (e1, e2)
    -> (
      let e1 = subst_free_vars e1 target_l sigma seen in
      let e2 = subst_free_vars e2 target_l sigma seen in
      match e with
      | Plus (_, _) -> Plus (e1, e2)
      | Minus (_, _) -> Minus (e1, e2)
      | Equal (_, _) -> Equal (e1, e2)
      | And (_, _) -> And (e1, e2)
      | Or (_, _) -> Or (e1, e2)
      | _ -> raise Unreachable [@coverage off])
  | Not e -> Not (subst_free_vars e target_l sigma seen)
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
  | FunResult { f; l; sigma } -> (
      match f with
      | Function (Ident x, e, l) ->
          FunResult
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
      | PlusOp (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> IntResult (i1 + i2)
          | _ -> raise TypeMismatch [@coverage off])
      | MinusOp (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> IntResult (i1 - i2)
          | _ -> raise TypeMismatch [@coverage off])
      | EqualOp (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> BoolResult (i1 = i2)
          | _ -> raise TypeMismatch [@coverage off])
      | AndOp (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | BoolResult b1, BoolResult b2 -> BoolResult (b1 && b2)
          | _ -> raise TypeMismatch [@coverage off])
      | OrOp (r1, r2) -> (
          let v1 = eval_result_value r1 in
          let v2 = eval_result_value r2 in
          match (v1, v2) with
          | BoolResult b1, BoolResult b2 -> BoolResult (b1 || b2)
          | _ -> raise TypeMismatch [@coverage off])
      | NotOp r -> (
          let v = eval_result_value r in
          match v with
          | BoolResult b -> BoolResult (not b)
          | _ -> raise TypeMismatch [@coverage off]))

let eval e ~is_debug_mode ~should_simplify =
  let e = transform_let e in
  fill_my_fun e None;
  let r = eval_aux e [] in

  if is_debug_mode then (
    (print_endline "****** Label Table ******";
     print_my_expr my_expr;
     print_endline "****** Label Table ******\n";
     print_endline "****** MyFun Table ******";
     print_my_fun my_fun;
     print_endline "****** MyFun Table ******\n")
    [@coverage off]);

  if not should_simplify then r
  else
    let v = eval_result_value r in
    Hashtbl.reset my_expr;
    Hashtbl.reset my_fun;
    v
