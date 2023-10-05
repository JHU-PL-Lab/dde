open Ast

exception TypeMismatch
exception Unreachable
exception Invalid_arg of string

type al = ALNil | ALCons of ((expr * al) * al)

type res =
  | ALFunRes of (expr * al)
  | ALIntRes of int
  | ALBoolRes of bool
  | ALPlusRes of (res * res)
  | ALMinusRes of (res * res)
  | ALEqRes of (res * res)
  | ALMultRes of (res * res)
  | ALGeRes of (res * res)
  | ALGtRes of (res * res)
  | ALLeRes of (res * res)
  | ALLtRes of (res * res)
  | ALAndRes of (res * res)
  | ALOrRes of (res * res)
  | ALNotRes of res

let rec eval_int = function
  | ALBoolRes _ | ALFunRes _ | ALEqRes _ | ALGeRes _ | ALGtRes _ | ALLeRes _
  | ALLtRes _ | ALAndRes _ | ALOrRes _ | ALNotRes _ ->
      raise TypeMismatch
  | ALIntRes i -> i
  | ALPlusRes (r1, r2) -> eval_int r1 + eval_int r2
  | ALMinusRes (r1, r2) -> eval_int r1 - eval_int r2
  | ALMultRes (r1, r2) -> eval_int r1 * eval_int r2

let rec eval_bool = function
  | ALIntRes _ | ALFunRes _ | ALPlusRes _ | ALMinusRes _ | ALMultRes _ ->
      raise TypeMismatch
  | ALBoolRes b -> b
  | ALEqRes (r1, r2) -> eval_int r1 = eval_int r2
  | ALGeRes (r1, r2) -> eval_int r1 >= eval_int r2
  | ALGtRes (r1, r2) -> eval_int r1 > eval_int r2
  | ALLeRes (r1, r2) -> eval_int r1 <= eval_int r2
  | ALLtRes (r1, r2) -> eval_int r1 < eval_int r2
  | ALAndRes (r1, r2) -> eval_bool r1 && eval_bool r2
  | ALOrRes (r1, r2) -> eval_bool r1 || eval_bool r2
  | ALNotRes r -> not (eval_bool r)

let ( => ) f al = ALCons (f, al)

let rec nth_exn al n =
  if n < 0 then raise (Invalid_arg "Negative index")
  else
    match al with
    | ALNil -> raise (Invalid_arg "Index of out of bounds")
    | ALCons (f, al) -> if n = 0 then f else nth_exn al (n - 1)

let rec eval expr al =
  match expr with
  | ALInt i -> ALIntRes i
  | ALBool b -> ALBoolRes b
  | ALFun _ -> ALFunRes (expr, al)
  | ALVar (Ident s, d) -> (
      Logs.info (fun m -> m "=== ALVar (%s, %d) ===" s d);
      let e_app, alm = nth_exn al d in
      match e_app with
      | ALApp (_, em') ->
          Logs.info (fun m -> m "*** ALVar (%s, %d) ***" s d);
          eval em' alm
      | _ -> raise Unreachable)
  | ALApp (e1, e2) -> (
      Logs.info (fun m -> m "=== ALApp ===");
      Logs.debug (fun m -> m "Evaluating %a" pp_expr expr);
      let fun_res = eval e1 al in
      match fun_res with
      | ALFunRes (e_fun, al1) -> (
          let _ = eval e2 al in
          match e_fun with
          | ALFun (_, e) ->
              Logs.info (fun m -> m "*** ALApp ***");
              eval e ((expr, al) => al1)
          | _ -> raise Unreachable)
      | _ -> raise Unreachable)
  | ALPlus (e1, e2) -> ALPlusRes (eval e1 al, eval e2 al)
  | ALMinus (e1, e2) -> ALMinusRes (eval e1 al, eval e2 al)
  | ALMult (e1, e2) -> ALMultRes (eval e1 al, eval e2 al)
  | ALEq (e1, e2) -> ALEqRes (eval e1 al, eval e2 al)
  | ALGe (e1, e2) -> ALGeRes (eval e1 al, eval e2 al)
  | ALGt (e1, e2) -> ALGtRes (eval e1 al, eval e2 al)
  | ALLe (e1, e2) -> ALLeRes (eval e1 al, eval e2 al)
  | ALLt (e1, e2) -> ALLtRes (eval e1 al, eval e2 al)
  | ALAnd (e1, e2) -> ALAndRes (eval e1 al, eval e2 al)
  | ALOr (e1, e2) -> ALOrRes (eval e1 al, eval e2 al)
  | ALNot e -> ALNotRes (eval e al)
  | ALIf (e1, e2, e3) ->
      Logs.info (fun m -> m "=== ALIf ===");
      let r1 = eval e1 al in
      if eval_bool r1 then (
        Logs.info (fun m -> m "=== ALIf True ===");
        let r2 = eval e2 al in
        Logs.info (fun m -> m "*** ALIf ***");
        r2)
      else (
        Logs.info (fun m -> m "=== ALIf False ===");
        let r3 = eval e3 al in
        Logs.info (fun m -> m "*** ALIf ***");
        r3)

let eval expr =
  let e = assign_depth expr in
  (* Format.printf "%a\n" pp_expr e; *)
  eval e ALNil

(* TODO: compare performance of interpreters *)
