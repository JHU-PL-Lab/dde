open Core
open Ast
open Exns

let rec eval_int = function
  | BoolRes _ | FunRes _ | RecRes _ | EqRes _ | AndRes _ | OrRes _ | GeRes _
  | GtRes _ | LeRes _ | LtRes _ | NotRes _ ->
      raise TypeMismatch
  | IntRes i -> i
  | PlusRes (r1, r2) -> eval_int r1 + eval_int r2
  | MinusRes (r1, r2) -> eval_int r1 - eval_int r2
  | MultRes (r1, r2) -> eval_int r1 * eval_int r2

let rec eval_bool = function
  | IntRes _ | FunRes _ | RecRes _ | PlusRes _ | MinusRes _ | MultRes _ ->
      raise TypeMismatch
  | BoolRes b -> b
  | EqRes (r1, r2) -> eval_int r1 = eval_int r2
  | AndRes (r1, r2) -> eval_bool r1 && eval_bool r2
  | OrRes (r1, r2) -> eval_bool r1 || eval_bool r2
  | GeRes (r1, r2) -> eval_int r1 >= eval_int r2
  | GtRes (r1, r2) -> eval_int r1 > eval_int r2
  | LeRes (r1, r2) -> eval_int r1 <= eval_int r2
  | LtRes (r1, r2) -> eval_int r1 < eval_int r2
  | NotRes r -> not (eval_bool r)

module Cache_key = struct
  module T = struct
    type lkey = int * sigma [@@deriving compare, sexp]
    type ekey = expr * sigma [@@deriving compare, sexp]
    type t = Lkey of lkey | Ekey of ekey [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module With_cache = struct
  module T = struct
    type cache = res Map.M(Cache_key).t
    type 'a t = cache -> 'a * cache

    let return (a : 'a) : 'a t = fun st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun c ->
      let a, c' = m c in
      f a c'

    let map = `Define_using_bind
    let get () : cache t = fun c -> (c, c)
    let set c : unit t = fun _ -> ((), c)
    let run (m : 'a t) = m (Map.empty (module Cache_key))
  end

  include T
  include Monad.Make (T)
end

open With_cache
open With_cache.Let_syntax

let cache key data : res T.t =
  let%bind c = get () in
  let%bind () = set (Map.add_exn (Map.remove c key) ~key ~data) in
  return data

(* can't do memoization like this in OCaml/Haskell; better laziness  *)
(* laziness + memoization *)
let rec eval_aux ~caching e sigma : res T.t =
  let%bind c = get () in
  match e with
  (* Value *)
  | Fun (ident, le', l) -> return (FunRes { f = e; l; sigma })
  | Int i -> return (IntRes i)
  | Bool b -> return (BoolRes b)
  (* Appication *)
  | App (e1, e2, app_l) -> (
      let cache_key = Cache_key.Lkey (app_l, sigma) in
      match Map.find c cache_key with
      | Some r when caching -> return r
      | _ ->
          let%bind r =
            match%bind eval_aux e1 sigma ~caching with
            | FunRes { f = Fun (id, e, f_l); l; sigma = sigma' } ->
                (* make sure e2 doesn't diverge - call-by-value-ish *)
                let%bind _ = eval_aux e2 sigma ~caching in
                eval_aux e (app_l :: sigma) ~caching
            | _ -> raise Unreachable
          in
          cache cache_key r)
  | Var (Ident x, l) -> (
      let cache_key = Cache_key.Ekey (e, sigma) in
      match Map.find c cache_key with
      | Some r when caching -> return r
      | _ -> (
          match get_myfun l with
          | Some (Fun (Ident x', _, _)) ->
              let%bind r =
                if String.(x = x') then
                  (* Var Local *)
                  match get_myexpr (List.hd_exn sigma) with
                  | App (_, e2, _) -> eval_aux e2 (List.tl_exn sigma) ~caching
                  | _ -> raise Unreachable
                else
                  (* Var Non-Local *)
                  match get_myexpr (List.hd_exn sigma) with
                  | App (e1, _, _) -> (
                      match%bind eval_aux e1 (List.tl_exn sigma) ~caching with
                      | FunRes { f; l = l1; sigma = sigma1 } ->
                          eval_aux (Var (Ident x, l1)) sigma1 ~caching
                      | _ -> raise Unreachable)
                  | _ -> raise Unreachable
              in
              cache cache_key r
          | _ -> raise Unreachable))
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
      let%bind r1 = eval_aux e1 sigma ~caching in
      let%bind r2 = eval_aux e2 sigma ~caching in
      return
        (match e with
        | Plus _ -> PlusRes (r1, r2)
        | Minus _ -> MinusRes (r1, r2)
        | Mult _ -> MultRes (r1, r2)
        | Eq _ -> EqRes (r1, r2)
        | And _ -> AndRes (r1, r2)
        | Or _ -> OrRes (r1, r2)
        | Ge _ -> GeRes (r1, r2)
        | Gt _ -> GtRes (r1, r2)
        | Le _ -> LeRes (r1, r2)
        | Lt _ -> LtRes (r1, r2)
        | _ -> raise Unreachable)
  | Not e ->
      let%bind r = eval_aux e sigma ~caching in
      return (NotRes r)
  | If (e1, e2, e3) ->
      let%bind r = eval_aux e1 sigma ~caching in
      if eval_bool r then eval_aux e2 sigma ~caching
      else eval_aux e3 sigma ~caching
  | Rec es ->
      es
      |> List.fold ~init:(return []) ~f:(fun acc (id, e) ->
             let%bind rs = acc in
             let%bind r = eval_aux ~caching e sigma in
             return ((id, r) :: rs))
      |> fun rs ->
      let%bind rs = rs in
      rs |> List.rev |> RecRes |> return
  | Proj (e, id) -> (
      match%bind eval_aux e sigma ~caching with
      | RecRes es -> (
          match List.find es ~f:(fun (x', _) -> compare_ident id x' = 0) with
          | Some (_, r) -> return r
          | None -> raise Runtime_error)
      | _ -> raise TypeMismatch)
  | Insp (id, e) -> (
      match%bind eval_aux e sigma ~caching with
      | RecRes es ->
          es
          |> List.exists ~f:(fun (x', _) -> compare_ident id x' = 0)
          |> BoolRes |> return
      | _ -> raise TypeMismatch)
  | LetAssert (_, e, _) -> eval_aux e sigma ~caching
  | Let _ -> raise Unreachable

let rec result_value_to_expr (r : res) : expr T.t =
  match r with
  | IntRes i -> return (Int i)
  | BoolRes b -> return (Bool b)
  | FunRes { f; l; sigma } -> return f
  | RecRes rs ->
      List.fold rs ~init:(return []) ~f:(fun acc (id, r) ->
          let%bind es = acc in
          let%bind e = result_value_to_expr r in
          return ((id, e) :: es))
      |> fun es ->
      let%bind es = es in
      return (Rec es)
  | PlusRes (r1, r2)
  | MinusRes (r1, r2)
  | MultRes (r1, r2)
  | EqRes (r1, r2)
  | AndRes (r1, r2)
  | OrRes (r1, r2)
  | GeRes (r1, r2)
  | GtRes (r1, r2)
  | LeRes (r1, r2)
  | LtRes (r1, r2) ->
      let%bind e1 = result_value_to_expr r1 in
      let%bind e2 = result_value_to_expr r2 in
      return
        (match r with
        | PlusRes _ -> Plus (e1, e2)
        | MinusRes _ -> Minus (e1, e2)
        | MultRes _ -> Mult (e1, e2)
        | EqRes _ -> Eq (e1, e2)
        | AndRes _ -> And (e1, e2)
        | OrRes _ -> Or (e1, e2)
        | GeRes _ -> Ge (e1, e2)
        | GtRes _ -> Gt (e1, e2)
        | LeRes _ -> Le (e1, e2)
        | LtRes _ -> Lt (e1, e2)
        | _ -> raise Unreachable)
  | NotRes r ->
      let%bind e = result_value_to_expr r in
      return (Not e)

let rec subst_free_vars e target_l sigma seen ~caching : expr T.t =
  match e with
  | Int _ -> return e
  | Bool _ -> return e
  | Fun (Ident x, e, l) ->
      let%bind e' =
        subst_free_vars e target_l sigma (String.Set.add seen x) ~caching
      in
      return (Fun (Ident x, e', l))
  | Var (Ident x, _) ->
      if String.Set.mem seen x then
        return e (* only substitute free variables *)
      else
        let%bind r = eval_aux (Var (Ident x, target_l)) sigma ~caching in
        let%bind r = eval_result_value r ~caching in
        result_value_to_expr r
  | App (e1, e2, l) ->
      let%bind e1' = subst_free_vars e1 target_l sigma seen ~caching in
      let%bind e2' = subst_free_vars e2 target_l sigma seen ~caching in
      return (App (e1', e2', l))
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
      let%bind e1 = subst_free_vars e1 target_l sigma seen ~caching in
      let%bind e2 = subst_free_vars e2 target_l sigma seen ~caching in
      return
        (match e with
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
  | Not e ->
      let%bind e = subst_free_vars e target_l sigma seen ~caching in
      return (Not e)
  | If (e1, e2, e3) ->
      let%bind e1' = subst_free_vars e1 target_l sigma seen ~caching in
      let%bind e2' = subst_free_vars e2 target_l sigma seen ~caching in
      let%bind e3' = subst_free_vars e3 target_l sigma seen ~caching in
      return (If (e1, e2, e3))
  | Rec es ->
      List.fold es ~init:(return []) ~f:(fun acc (id, e) ->
          let%bind es' = acc in
          let%bind e' = subst_free_vars e target_l sigma seen ~caching in
          return ((id, e') :: es'))
      |> fun es' ->
      let%bind es' = es' in
      es' |> List.rev |> Rec |> return
  | Proj (e, id) ->
      let%bind e' = subst_free_vars e target_l sigma seen ~caching in
      return (Proj (e', id))
  | Insp (id, e) ->
      let%bind e' = subst_free_vars e target_l sigma seen ~caching in
      return (Insp (id, e'))
  (* ignore letassert *)
  | LetAssert (_, e, _) -> subst_free_vars e target_l sigma seen ~caching
  | Let _ -> raise Unreachable

and eval_result_value r ~caching : res T.t =
  match r with
  | IntRes i -> return r
  | BoolRes b -> return r
  | FunRes { f; l; sigma } -> (
      match f with
      | Fun (Ident x, e, l) ->
          let%bind e' =
            subst_free_vars e l sigma (String.Set.singleton x) ~caching
          in
          return (FunRes { f = Fun (Ident x, e', l); l; sigma })
      | _ -> raise Unreachable)
  | PlusRes (r1, r2)
  | MinusRes (r1, r2)
  | MultRes (r1, r2)
  | EqRes (r1, r2)
  | GeRes (r1, r2)
  | GtRes (r1, r2)
  | LeRes (r1, r2)
  | LtRes (r1, r2) -> (
      let%bind r1' = eval_result_value r1 ~caching in
      let%bind r2' = eval_result_value r2 ~caching in
      match (r1', r2') with
      | IntRes i1, IntRes i2 ->
          return
            (match r with
            | PlusRes _ -> IntRes (i1 + i2)
            | MinusRes _ -> IntRes (i1 - i2)
            | MultRes _ -> IntRes (i1 * i2)
            | EqRes _ -> BoolRes (i1 = i2)
            | GeRes _ -> BoolRes (i1 >= i2)
            | GtRes _ -> BoolRes (i1 > i2)
            | LeRes _ -> BoolRes (i1 <= i2)
            | LtRes _ -> BoolRes (i1 < i2)
            | _ -> raise Unreachable)
      | _ -> raise TypeMismatch)
  | AndRes (r1, r2) | OrRes (r1, r2) -> (
      let%bind r1' = eval_result_value r1 ~caching in
      let%bind r2' = eval_result_value r2 ~caching in
      match (r1', r2') with
      | BoolRes b1, BoolRes b2 ->
          return
            (match r with
            | AndRes _ -> BoolRes (b1 && b2)
            | OrRes _ -> BoolRes (b1 || b2)
            | _ -> raise Unreachable)
      | _ -> raise TypeMismatch)
  | NotRes r ->
      let%bind r' = eval_result_value r ~caching in
      return
        (match r' with BoolRes b -> BoolRes (not b) | _ -> raise TypeMismatch)
  | RecRes rs ->
      List.fold rs ~init:(return []) ~f:(fun acc (id, r) ->
          let%bind rs' = acc in
          let%bind r' = eval_result_value r ~caching in
          return ((id, r') :: rs'))
      |> fun es' ->
      let%bind es' = es' in
      es' |> List.rev |> RecRes |> return

let eval ?(caching = true) ?(debug = false) ?(simplify = false) e =
  build_myfun e None;
  let e = trans_let None None e in

  let start_time = Stdlib.Sys.time () in
  let r, c = run (eval_aux e [] ~caching) in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  if debug then (
    print_string (Pp.string_of_table myexpr "myexpr");
    print_string (Pp.string_of_table myfun "myfun"));

  let r' = if simplify then fst (eval_result_value r ~caching c) else r in
  clean_up ();

  (r', runtime)
