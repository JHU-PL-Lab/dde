(** Core algorithm of interpreter per paper Section 2.2 *)

open Core
open Logs
open Ast
open Res
open Exns

let rec eval_int = function
  | Res.BoolRes _ | FunRes _ | RecRes _ | EqRes _ | AndRes _ | OrRes _ | GeRes _
  | GtRes _ | LeRes _ | LtRes _ | NotRes _ ->
      raise TypeMismatch
  | IntRes i -> i
  | PlusRes (r1, r2) -> eval_int r1 + eval_int r2
  | MinusRes (r1, r2) -> eval_int r1 - eval_int r2
  | MultRes (r1, r2) -> eval_int r1 * eval_int r2

let rec eval_bool = function
  | Res.IntRes _ | FunRes _ | RecRes _ | PlusRes _ | MinusRes _ | MultRes _ ->
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
    (* Cache key for applications (can be uniquely identified by its label) *)
    type lkey = int * sigma [@@deriving compare, sexp]

    (* Cache key for variables (can't be uniquely identified by just the label
       due to decrementing de Bruijn indices) *)
    type ekey = Expr.t * sigma [@@deriving compare, sexp]
    type t = Lkey of lkey | Ekey of ekey [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

(** State Monad threading the cache through the interpreter *)
module With_cache = struct
  module T = struct
    type cache = Res.t Map.M(Cache_key).t
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

(** Caches the interpreter result *)
let cache key data : Res.t T.t =
  let%bind c = get () in
  let%bind () = set (Map.add_exn (Map.remove c key) ~key ~data) in
  return data

(** Main interpreter algorithm per paper Fig. 5 *)
let rec eval_aux ~caching d expr sigma : Res.t T.t =
  let%bind c = get () in
  let d = d + 1 in
  match expr with
  (* Value rule *)
  | Expr.Int i -> return (IntRes i)
  | Bool b -> return (BoolRes b)
  (* Value Fun rule *)
  | Fun (ident, le', _) -> return (FunRes (expr, sigma))
  (* Appication rule *)
  | App (e1, e2, l) -> (
      info (fun m -> m "[Level %d] === App %a ===" d Expr.pp expr);
      let cache_key = Cache_key.Lkey (l, sigma) in
      match Map.find c cache_key with
      (* Cache hit *)
      | Some r when caching ->
          debug (fun m -> m "[Level %d] Cache hit" d);
          return r
      | _ -> (
          debug (fun m -> m "[Level %d] No hit" d);
          debug (fun m -> m "[Level %d] Stack: %a" d pp_sigma sigma);
          debug (fun m -> m "[Level %d] Eval fun: %a" d Expr.pp e1);
          match%bind eval_aux d e1 sigma ~caching with
          | FunRes (Fun (id, e, _), sigma') ->
              (* Make sure e2 doesn't diverge - call-by-value-ish *)
              (* debug (fun m ->
                     m "[Level %d] Eval arg to check non-divergence: %a" d
                       Expr.pp e2);
                 let%bind _ = eval_aux e2 sigma ~caching in *)
              debug (fun m -> m "[Level %d] Eval fun body: %a" d Expr.pp e);
              let%bind r = eval_aux d e (l :: sigma) ~caching in
              info (fun m -> m "[Level %d] *** App %a ***" d Expr.pp expr);
              cache cache_key r
          | _ -> raise Unreachable))
  (* Var rules *)
  | Var (id, i) -> (
      info (fun m -> m "[Level %d] === Var %a@%d ===" d Ident.pp id i);
      let cache_key = Cache_key.Ekey (expr, sigma) in
      match Map.find c cache_key with
      (* Cache hit *)
      | Some r when caching ->
          debug (fun m -> m "[Level %d] Cache hit" d);
          return r
      | _ -> (
          debug (fun m -> m "[Level %d] No hit" d);
          debug (fun m -> m "[Level %d] Stack: %a" d pp_sigma sigma);
          let sigma_hd, sigma_tl = (List.hd_exn sigma, List.tl_exn sigma) in
          match get_myexpr sigma_hd with
          | App (e1, e2, _) as app ->
              debug (fun m -> m "[Level %d] App at stack top: %a" d Expr.pp app);
              if i = 0 then (
                (* Var Local rule *)
                debug (fun m ->
                    m "[Level %d] Local, eval app arg: %a" d Expr.pp e2);
                let%bind r = eval_aux d e2 sigma_tl ~caching in
                info (fun m ->
                    m "[Level %d] *** Var Local %a@%d ***" d Ident.pp id i);
                cache cache_key r)
              else (
                (* Var Non-Local rule *)
                debug (fun m ->
                    m "[Level %d] Non-Local, eval fun at stack top: %a" d
                      Expr.pp e1);
                match%bind eval_aux d e1 sigma_tl ~caching with
                | FunRes (_, sigma1) ->
                    debug (fun m ->
                        m "[Level %d] Decrement index to %d and eval" d (i - 1));
                    let%bind r = eval_aux d (Var (id, i - 1)) sigma1 ~caching in
                    info (fun m ->
                        m "[Level %d] *** Var Non-Local %a@%d ***" d Ident.pp id
                          i);
                    cache cache_key r
                | _ -> raise Unreachable)
          | _ -> raise Unreachable))
  (* Operation rule *)
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
      let%bind r1 = eval_aux d e1 sigma ~caching in
      let%bind r2 = eval_aux d e2 sigma ~caching in
      return
        (match expr with
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
      let%bind r = eval_aux d e sigma ~caching in
      return (NotRes r)
  (* Conditional rule *)
  | If (e1, e2, e3) ->
      let%bind r = eval_aux d e1 sigma ~caching in
      if eval_bool r then eval_aux d e2 sigma ~caching
      else eval_aux d e3 sigma ~caching
  (* Record Value rule *)
  | Rec es ->
      es
      |> List.fold ~init:(return []) ~f:(fun acc (id, e) ->
             let%bind rs = acc in
             let%bind r = eval_aux d ~caching e sigma in
             return ((id, r) :: rs))
      |> fun rs ->
      let%bind rs = rs in
      rs |> List.rev |> RecRes |> return
  (* Record Project rule *)
  | Proj (e, id) -> (
      match%bind eval_aux d e sigma ~caching with
      | RecRes es -> (
          match List.find es ~f:(fun (x', _) -> Ident.(id = x')) with
          | Some (_, r) -> return r
          | None -> raise Runtime_error)
      | _ -> raise TypeMismatch)
  (* Record Inspect rule *)
  | Insp (id, e) -> (
      match%bind eval_aux d e sigma ~caching with
      | RecRes es ->
          es
          |> List.exists ~f:(fun (x', _) -> Ident.(id = x'))
          |> BoolRes |> return
      | _ -> raise TypeMismatch)
  | LetAssert (_, e, _) -> eval_aux d e sigma ~caching
  | Let _ -> raise Unreachable

(** Helper to convert a result to an expression *)
let rec result_value_to_expr r : Expr.t T.t =
  let open Expr in
  match r with
  | IntRes i -> return (Int i)
  | BoolRes b -> return (Bool b)
  | FunRes (f, _) -> return f
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

(** Helper to substitute free variables in an expression.
    Not used in core algorithm, but rather only to help
    simplify the final result *)
let rec subst_free_vars e sigma seen var ~caching : Expr.t T.t =
  let open Expr in
  match e with
  | Int _ -> return e
  | Bool _ -> return e
  | Fun (Ident x, e, l) ->
      let%bind e' =
        subst_free_vars e sigma (String.Set.add seen x) var ~caching
      in
      return (Fun (Ident x, e', l))
  | Var (Ident x, _) ->
      if String.Set.mem seen x then
        return e (* Only substitute free variables *)
      else
        let%bind r = eval_aux 0 var sigma ~caching in
        let%bind r = eval_result_value r ~caching in
        result_value_to_expr r
  | App (e1, e2, l) ->
      let%bind e1' = subst_free_vars e1 sigma seen var ~caching in
      let%bind e2' = subst_free_vars e2 sigma seen var ~caching in
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
      let%bind e1 = subst_free_vars e1 sigma seen var ~caching in
      let%bind e2 = subst_free_vars e2 sigma seen var ~caching in
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
      let%bind e = subst_free_vars e sigma seen var ~caching in
      return (Not e)
  | If (e1, e2, e3) ->
      let%bind e1' = subst_free_vars e1 sigma seen var ~caching in
      let%bind e2' = subst_free_vars e2 sigma seen var ~caching in
      let%bind e3' = subst_free_vars e3 sigma seen var ~caching in
      return (If (e1, e2, e3))
  | Rec es ->
      List.fold es ~init:(return []) ~f:(fun acc (id, e) ->
          let%bind es' = acc in
          let%bind e' = subst_free_vars e sigma seen var ~caching in
          return ((id, e') :: es'))
      |> fun es' ->
      let%bind es' = es' in
      es' |> List.rev |> Rec |> return
  | Proj (e, id) ->
      let%bind e' = subst_free_vars e sigma seen var ~caching in
      return (Proj (e', id))
  | Insp (id, e) ->
      let%bind e' = subst_free_vars e sigma seen var ~caching in
      return (Insp (id, e'))
  (* ignore letassert *)
  | LetAssert (_, e, _) -> subst_free_vars e sigma seen var ~caching
  | Let _ -> raise Unreachable

(** Helper to evaluate the final result so as to simplify it.
    This is needed as our language doesn't substitute variable bindings
    in a closure. E.g., C[fun x -> y] where C holds y = 1, so it can be
    simplified to fun x -> 1. *)
and eval_result_value r ~caching : Res.t T.t =
  match r with
  | IntRes i -> return r
  | BoolRes b -> return r
  | FunRes (f, sigma) -> (
      match f with
      | Fun ((Ident x as id), e, sv) ->
          let var =
            (* Find the variable of the same name that can be looked up to
               a value starting from this function *)
            List.find_exn sv ~f:(function
              | Var (id', _) -> Ident.(id = id')
              | _ -> raise Unreachable)
          in
          let%bind e' =
            subst_free_vars e sigma (String.Set.singleton x) var ~caching
          in
          return (FunRes (Fun (id, e', sv), sigma))
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

(** Entry point to interpreter *)
let eval ?(caching = true) ?(debug = false) ?(simplify = false) e =
  let e = e |> subst_let None None |> assign_index |> scope_vars in

  (* Format.printf "%a\n" Expr.pp e; *)
  let start_time = Stdlib.Sys.time () in
  let r, c = run (eval_aux 0 e [] ~caching) in
  let end_time = Stdlib.Sys.time () in
  let runtime = end_time -. start_time in

  if debug then print_string (string_of_table myexpr "myexpr");

  let r' = if simplify then fst (eval_result_value r ~caching c) else r in
  clean_up ();

  (* Format.printf "Result: %a\n" Res.pp r'; *)
  (r', runtime)
