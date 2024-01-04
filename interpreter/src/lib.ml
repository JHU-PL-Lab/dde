open Ast

exception TypeMismatch
exception Unreachable

let rec eval_int = function
  | BoolResult _ | FunResult _ | RecordResult _ -> raise TypeMismatch
  | IntResult i -> i
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2) -> eval_int r1 + eval_int r2
      | MinusOp (r1, r2) -> eval_int r1 - eval_int r2
      | MultOp (r1, r2) -> eval_int r1 * eval_int r2
      | EqOp _ | AndOp _ | OrOp _ | GeOp _ | GtOp _ | LeOp _ | LtOp _ | NotOp _
        ->
          raise TypeMismatch)

let rec eval_bool = function
  | IntResult _ | FunResult _ | RecordResult _ -> raise TypeMismatch
  | BoolResult b -> b
  | OpResult op_r -> (
      match op_r with
      | PlusOp _ | MinusOp _ | MultOp _ -> raise TypeMismatch
      | EqOp (r1, r2) -> eval_int r1 = eval_int r2
      | AndOp (r1, r2) -> eval_bool r1 && eval_bool r2
      | OrOp (r1, r2) -> eval_bool r1 || eval_bool r2
      | GeOp (r1, r2) -> eval_int r1 >= eval_int r2
      | GtOp (r1, r2) -> eval_int r1 > eval_int r2
      | LeOp (r1, r2) -> eval_int r1 <= eval_int r2
      | LtOp (r1, r2) -> eval_int r1 < eval_int r2
      | NotOp r -> not (eval_bool r))

let memo_cache = Hashtbl.create 10000

(* can't do memoization like this in OCaml/Haskell; better laziness  *)
(* laziness + memoization *)
let rec eval_aux e sigma ~should_cache =
  match Hashtbl.find_opt memo_cache (e, sigma) with
  | Some res when should_cache ->
      (* Format.printf "cache hit\n"; *)
      res
  | _ ->
      let eval_res =
        match e with
        (* Value *)
        | Function (ident, le', l) -> FunResult { f = e; l; sigma }
        | Int i -> IntResult i
        | Bool b -> BoolResult b
        (* Application *)
        | Appl (e1, e2, app_l) -> (
            match eval_aux e1 sigma ~should_cache with
            | FunResult { f = Function (id, e, f_l); l; sigma = sigma' } ->
                (* make sure e2 doesn't diverge - call-by-value-ish *)
                let _ = eval_aux e2 sigma ~should_cache in
                eval_aux e (app_l :: sigma) ~should_cache
            | _ -> raise Unreachable)
        | Var (Ident x, l) -> (
            match get_myfun l with
            | Some (Function (Ident x', _, _)) -> (
                if x = x' then
                  (* Var Local *)
                  match get_myexpr (List.hd sigma) with
                  | Appl (_, e2, _) -> eval_aux e2 (List.tl sigma) ~should_cache
                  | _ -> raise Unreachable
                else
                  (* Var Non-Local *)
                  match get_myexpr (List.hd sigma) with
                  | Appl (e1, _, _) -> (
                      match eval_aux e1 (List.tl sigma) ~should_cache with
                      | FunResult { f; l = l1; sigma = sigma1 } ->
                          eval_aux (Var (Ident x, l1)) sigma1 ~should_cache
                      | _ -> raise Unreachable)
                  | _ -> raise Unreachable)
            | _ -> raise Unreachable)
        | Plus (e1, e2)
        | Minus (e1, e2)
        | Mult (e1, e2)
        | Eq (e1, e2)
        | And (e1, e2)
        | Or (e1, e2)
        | Ge (e1, e2)
        | Gt (e1, e2)
        | Le (e1, e2)
        | Lt (e1, e2) ->
            let r1 = eval_aux e1 sigma ~should_cache in
            let r2 = eval_aux e2 sigma ~should_cache in
            OpResult
              (match e with
              | Plus _ -> PlusOp (r1, r2)
              | Minus _ -> MinusOp (r1, r2)
              | Mult _ -> MultOp (r1, r2)
              | Eq _ -> EqOp (r1, r2)
              | And _ -> AndOp (r1, r2)
              | Or _ -> OrOp (r1, r2)
              | Ge _ -> GeOp (r1, r2)
              | Gt _ -> GtOp (r1, r2)
              | Le _ -> LeOp (r1, r2)
              | Lt _ -> LtOp (r1, r2)
              | _ -> raise Unreachable)
        | Not e -> OpResult (NotOp (eval_aux e sigma ~should_cache))
        | If (e1, e2, e3, _) ->
            let r = eval_aux e1 sigma ~should_cache in
            if eval_bool r then eval_aux e2 sigma ~should_cache
            else eval_aux e3 sigma ~should_cache
        | Record entries ->
            RecordResult
              (List.map
                 (fun (x, e) -> (x, eval_aux e sigma ~should_cache))
                 entries)
        | Projection (e, x) -> (
            match eval_aux e sigma ~should_cache with
            | RecordResult entries ->
                snd (List.find (fun (x', _) -> x = x') entries)
            | _ -> raise TypeMismatch)
        | Inspection (x, e) -> (
            match eval_aux e sigma ~should_cache with
            | RecordResult entries ->
                BoolResult (List.exists (fun (x', _) -> x = x') entries)
            | _ -> raise TypeMismatch)
        | LetAssert (_, e, _) ->
            (* TODO: still assert *)
            eval_aux e sigma ~should_cache
        | Let _ -> raise Unreachable
      in
      if should_cache then Hashtbl.replace memo_cache (e, sigma) eval_res;
      eval_res

module StringSet = Set.Make (String)

let rec result_value_to_expr (r : result_value) : expr =
  match r with
  | IntResult i -> Int i
  | BoolResult b -> Bool b
  | FunResult { f; l; sigma } -> f
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2)
      | MinusOp (r1, r2)
      | MultOp (r1, r2)
      | EqOp (r1, r2)
      | AndOp (r1, r2)
      | OrOp (r1, r2)
      | GeOp (r1, r2)
      | GtOp (r1, r2)
      | LeOp (r1, r2)
      | LtOp (r1, r2) -> (
          let e1 = result_value_to_expr r1 in
          let e2 = result_value_to_expr r2 in
          match op with
          | PlusOp _ -> Plus (e1, e2)
          | MinusOp _ -> Minus (e1, e2)
          | MultOp _ -> Mult (e1, e2)
          | EqOp _ -> Eq (e1, e2)
          | AndOp _ -> And (e1, e2)
          | OrOp _ -> Or (e1, e2)
          | GeOp _ -> Ge (e1, e2)
          | GtOp _ -> Gt (e1, e2)
          | LeOp _ -> Le (e1, e2)
          | LtOp _ -> Lt (e1, e2)
          | NotOp _ -> raise Unreachable)
      | NotOp r -> Not (result_value_to_expr r))
  | RecordResult entries ->
      Record (List.map (fun (x, v) -> (x, result_value_to_expr v)) entries)

let rec subst_free_vars e target_l sigma seen ~should_cache =
  match e with
  | Int _ -> e
  | Bool _ -> e
  | Function (Ident x, e', l) ->
      Function
        ( Ident x,
          subst_free_vars e' target_l sigma (StringSet.add x seen) ~should_cache,
          l )
  | Var (Ident x, _) ->
      if StringSet.mem x seen then e (* only substitute free variables *)
      else
        eval_aux (Var (Ident x, target_l)) sigma ~should_cache
        |> eval_result_value ~should_cache
        |> result_value_to_expr
  | Appl (e1, e2, l) ->
      Appl
        ( subst_free_vars e1 target_l sigma seen ~should_cache,
          subst_free_vars e2 target_l sigma seen ~should_cache,
          l )
  | Plus (e1, e2)
  | Minus (e1, e2)
  | Mult (e1, e2)
  | Eq (e1, e2)
  | And (e1, e2)
  | Or (e1, e2)
  | Ge (e1, e2)
  | Gt (e1, e2)
  | Le (e1, e2)
  | Lt (e1, e2) -> (
      let e1 = subst_free_vars e1 target_l sigma seen ~should_cache in
      let e2 = subst_free_vars e2 target_l sigma seen ~should_cache in
      match e with
      | Plus _ -> Plus (e1, e2)
      | Minus _ -> Minus (e1, e2)
      | Mult _ -> Mult (e1, e2)
      | Eq _ -> Eq (e1, e2)
      | And _ -> And (e1, e2)
      | Or _ -> Or (e1, e2)
      | Ge _ -> Ge (e1, e2)
      | Gt _ -> Gt (e1, e2)
      | Le _ -> Le (e1, e2)
      | Lt _ -> Lt (e1, e2)
      | _ -> raise Unreachable)
  | Not e -> Not (subst_free_vars e target_l sigma seen ~should_cache)
  | If (e1, e2, e3, l) ->
      If
        ( subst_free_vars e1 target_l sigma seen ~should_cache,
          subst_free_vars e2 target_l sigma seen ~should_cache,
          subst_free_vars e3 target_l sigma seen ~should_cache,
          l )
  | Record entries ->
      Record
        (List.map
           (fun (x, e) ->
             (x, subst_free_vars e target_l sigma seen ~should_cache))
           entries)
  | Projection (e, x) ->
      Projection (subst_free_vars e target_l sigma seen ~should_cache, x)
  | Inspection (x, e) ->
      Inspection (x, subst_free_vars e target_l sigma seen ~should_cache)
  (* ignore letassert *)
  | LetAssert (_, e, _) -> subst_free_vars e target_l sigma seen ~should_cache
  | Let _ -> raise Unreachable

and eval_result_value r ~should_cache =
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
                  ( Ident x,
                    subst_free_vars e l sigma (StringSet.singleton x)
                      ~should_cache,
                    l );
              l;
              sigma;
            }
      | _ -> raise Unreachable)
  | OpResult op -> (
      match op with
      | PlusOp (r1, r2)
      | MinusOp (r1, r2)
      | MultOp (r1, r2)
      | EqOp (r1, r2)
      | GeOp (r1, r2)
      | GtOp (r1, r2)
      | LeOp (r1, r2)
      | LtOp (r1, r2) -> (
          let v1 = eval_result_value r1 ~should_cache in
          let v2 = eval_result_value r2 ~should_cache in
          match (v1, v2) with
          | IntResult i1, IntResult i2 -> (
              match op with
              | PlusOp _ -> IntResult (i1 + i2)
              | MinusOp _ -> IntResult (i1 - i2)
              | MultOp _ -> IntResult (i1 * i2)
              | EqOp _ -> BoolResult (i1 = i2)
              | GeOp _ -> BoolResult (i1 >= i2)
              | GtOp _ -> BoolResult (i1 > i2)
              | LeOp _ -> BoolResult (i1 <= i2)
              | LtOp _ -> BoolResult (i1 < i2)
              | _ -> raise Unreachable)
          | _ -> raise TypeMismatch)
      | AndOp (r1, r2) | OrOp (r1, r2) -> (
          let v1 = eval_result_value r1 ~should_cache in
          let v2 = eval_result_value r2 ~should_cache in
          match (v1, v2) with
          | BoolResult b1, BoolResult b2 -> (
              match op with
              | AndOp _ -> BoolResult (b1 && b2)
              | OrOp _ -> BoolResult (b1 || b2)
              | _ -> raise Unreachable)
          | _ -> raise TypeMismatch)
      | NotOp r -> (
          let v = eval_result_value r ~should_cache in
          match v with
          | BoolResult b -> BoolResult (not b)
          | _ -> raise TypeMismatch))
  | RecordResult entries ->
      RecordResult
        (List.map
           (fun (x, r) -> (x, eval_result_value r ~should_cache))
           entries)

let print_myexpr tbl =
  Core.Hashtbl.to_alist tbl
  |> Core.List.sort ~compare:(fun (k1, v1) (k2, v2) -> compare k1 k2)
  |> Core.List.iter ~f:(fun (k, v) -> Format.printf "%d -> %a\n" k Pp.pp_expr v)
  [@@coverage off]

let print_myfun tbl =
  Core.Hashtbl.iteri
    ~f:(fun ~key ~data -> Format.printf "%d -> %s\n" key (show_expr data))
    tbl
  [@@coverage off]

let eval ?(should_cache = true) ~is_debug_mode ~should_simplify e =
  build_myfun e None;
  let e = trans_let None None e in
  let r = eval_aux e [] ~should_cache in

  if is_debug_mode then (
    print_endline "****** Label Table ******";
    print_myexpr myexpr;
    print_endline "****** Label Table ******\n";
    print_endline "****** MyFun Table ******";
    print_myfun myfun;
    print_endline "****** MyFun Table ******\n");

  if should_simplify then (
    let v = eval_result_value r ~should_cache in
    clean_up ();
    v)
  else (
    clean_up ();
    r)
