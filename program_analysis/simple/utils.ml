(** Utility data structures and functions *)

open Core
open Logs
open Interp.Ast

let ff = Format.fprintf

module Sigma = struct
  module T = struct
    type t = sigma [@@deriving compare, sexp, show { with_path = false }]
  end

  include T
  include Comparable.Make (T)
end

(** Stub labels *)
module St = struct
  module T = struct
    type lstate = int * sigma [@@deriving compare, sexp]
    type estate = Expr.t * sigma [@@deriving compare, sexp]
    type t = Lstate of lstate | Estate of estate [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

(** S set containing all seen call stacks *)
module S = struct
  module T = struct
    type t = Set.M(Sigma).t [@@deriving compare, sexp]

    let pp fmt (s : t) =
      s |> Set.elements |> List.map ~f:Sigma.show |> String.concat ~sep:", "
      |> Format.fprintf fmt "{%s}"

    let show (s : t) =
      s |> Set.elements |> List.map ~f:Sigma.show |> String.concat ~sep:", "
      |> Format.sprintf "{%s}"
  end

  include T
  include Comparable.Make (T)
end

module V_key = struct
  module T = struct
    type lstate = int * sigma * int [@@deriving compare, sexp]

    let pp_lstate fmt (l, sigma, sid) =
      Format.fprintf fmt "(%d, %a, %d)" l Sigma.pp sigma sid

    let show_lstate (l, sigma, sid) =
      Format.sprintf "(%d, %s, %d)" l (Sigma.show sigma) sid

    type estate = Expr.t * sigma * int [@@deriving compare, sexp]

    let pp_estate fmt (e, sigma, sid) =
      Format.fprintf fmt "(%a, %a, %d)" Interp.Pp.pp_expr e Sigma.pp sigma sid

    let show_estate (e, sigma, sid) =
      Format.asprintf "(%a, %s, %d)" Interp.Pp.pp_expr e (Sigma.show sigma) sid

    type t = Lstate of lstate | Estate of estate [@@deriving compare, sexp]

    let pp fmt (k : t) =
      match k with
      | Lstate st -> pp_lstate fmt st
      | Estate st -> pp_estate fmt st

    let show (k : t) =
      match k with Lstate st -> show_lstate st | Estate st -> show_estate st
  end

  include T
  include Comparable.Make (T)
end

(** V set containing all seen program states *)
module V = struct
  module T = struct
    type t = Set.M(V_key).t [@@deriving compare, sexp]

    let pp fmt (v : t) =
      v |> Set.elements |> List.map ~f:V_key.show |> String.concat ~sep:", "
      |> Format.fprintf fmt "{%s}"

    let show (v : t) =
      v |> Set.elements |> List.map ~f:V_key.show |> String.concat ~sep:", "
      |> Format.sprintf "{%s}"
  end

  include T
  include Comparable.Make (T)
end

module Freq_key = struct
  module T = struct
    type t = Expr.t * sigma * int * int [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

(** Value atom - no labeled results (starts to cycles) or path conditions *)
module rec Atom : sig
  type t =
    | IntAnyAtom
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of Expr.t * sigma
    | LStubAtom of (int * sigma)
    | EStubAtom of (Expr.t * sigma)
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving compare, sexp]

  val pp : Format.formatter -> Atom.t -> unit
end = struct
  type t =
    | IntAnyAtom
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of Expr.t * sigma
    | LStubAtom of (int * sigma)
    | EStubAtom of (Expr.t * sigma)
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving compare, sexp]

  let rec pp_record fmt = function
    | [] -> ()
    | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x Res.pp v
    | (Ident x, r) :: rest ->
        Format.fprintf fmt "%s = %a; %a" x Res.pp r pp_record rest

  and pp fmt = function
    | IntAnyAtom -> ff fmt "Int"
    | IntAtom i -> ff fmt "%d" i
    | BoolAtom b -> ff fmt "%b" b
    | FunAtom (f, _) -> Interp.Pp.pp_expr fmt f
    | LStubAtom (l, sigma) ->
        (* ff fmt "stub@(%d,%a)" l pp_sigma sigma *)
        ff fmt "stub"
    | EStubAtom (e, sigma) ->
        (* ff fmt "stub@(%a,%a)" Interp.Pp.pp_expr e pp_sigma sigma *)
        ff fmt "stub"
    | RecAtom entries ->
        ff fmt
          (if List.length entries = 0 then "{%a}" else "{ %a }")
          pp_record entries
    | ProjAtom (r, Ident s) -> ff fmt "(%a.%s)" Res.pp r s
    | InspAtom (Ident s, r) -> ff fmt "(%s in %a)" s Res.pp r
    | AssertAtom (_, r, _) -> ff fmt "%a" Res.pp r
end

and Res_key : sig
  type t = Atom.t [@@deriving compare, sexp]
  type comparator_witness

  val comparator : (t, comparator_witness) Comparator.t
end = struct
  module T = struct
    type t = Atom.t [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

(** Value result *)
and Res : sig
  type t = Set.M(Res_key).t [@@deriving compare, sexp]

  val pp : Format.formatter -> t -> unit
  val show : t -> string
end = struct
  type t = Set.M(Res_key).t [@@deriving compare, sexp]

  let rec pp_aux fmt = function
    | [] -> ()
    | [ a ] -> ff fmt "%a" Atom.pp a
    | a :: _as -> ff fmt "(%a | %a)" Atom.pp a pp_aux _as

  and pp fmt r =
    if Set.is_empty r then ff fmt "#" else ff fmt "%a" pp_aux (Set.elements r)

  let show (r : t) = Format.asprintf "%a" pp r
end

module Cache_key = struct
  module T = struct
    type lkey = int * sigma * int * int [@@deriving compare, sexp]
    type ekey = Expr.t * sigma * int * int [@@deriving compare, sexp]
    type t = Lkey of lkey | Ekey of ekey [@@deriving compare, sexp]

    let pp_lkey fmt (l, sigma, vid, sid) =
      Format.fprintf fmt "(%d, %a, %d, %d)" l Sigma.pp sigma vid sid

    let show_lkey (l, sigma, vid, sid) =
      Format.asprintf "(%d, %a, %d, %d)" l Sigma.pp sigma vid sid

    let pp_ekey fmt (expr, sigma, vid, sid) =
      Format.fprintf fmt "(%a, %a, %d, %d)" Interp.Pp.pp_expr expr Sigma.pp
        sigma vid sid

    let show_ekey (expr, sigma, vid, sid) =
      Format.asprintf "(%a, %a, %d, %d)" Interp.Pp.pp_expr expr Sigma.pp sigma
        vid sid

    let pp fmt = function
      | Lkey lkey -> pp_lkey fmt lkey
      | Ekey ekey -> pp_ekey fmt ekey

    let show = function
      | Lkey lkey -> show_lkey lkey
      | Ekey ekey -> show_ekey ekey

    (* type lkey = int * sigma * int [@@deriving compare, sexp]
       type ekey = expr * sigma * int [@@deriving compare, sexp]
       type t = Lkey of lkey | Ekey of ekey [@@deriving compare, sexp]

       let pp_lkey fmt (l, sigma, sid) =
         Format.fprintf fmt "(%d, %a, %d)" l Sigma.pp sigma sid

       let show_lkey (l, sigma, sid) =
         Format.asprintf "(%d, %a, %d)" l Sigma.pp sigma sid

       let pp_ekey fmt (expr, sigma, sid) =
         Format.fprintf fmt "(%a, %a, %d)" Interp.Pp.pp_expr expr Sigma.pp sigma
           sid

       let show_ekey (expr, sigma, sid) =
         Format.asprintf "(%a, %a, %d)" Interp.Pp.pp_expr expr Sigma.pp sigma sid

       let pp fmt = function
         | Lkey lkey -> pp_lkey fmt lkey
         | Ekey ekey -> pp_ekey fmt ekey

       let show = function
         | Lkey lkey -> show_lkey lkey
         | Ekey ekey -> show_ekey ekey *)
  end

  include T
  include Comparable.Make (T)
end

let empty_res = Set.empty (module Res_key)
let single_res = Set.singleton (module Res_key)

(** Reader-State monad threaded through the simple analysis *)
module ReaderState = struct
  module T = struct
    type cache = Res.t Map.M(Cache_key).t
    type vids = int Map.M(V).t
    type sids = int Map.M(S).t
    type env = { v : V.t; vids : vids }
    type state = { s : S.t; c : cache; sids : sids; cnt : int }
    type 'a t = env -> state -> 'a * state

    let return (a : 'a) : 'a t = fun _ st -> (a, st)

    let bind (m : 'a t) ~(f : 'a -> 'b t) : 'b t =
     fun env st ->
      let a, st' = m env st in
      f a env st'

    let map = `Define_using_bind
    let ask () : env t = fun env st -> (env, st)

    let local d (f : env -> env) (m : 'a t) : 'a t =
     fun env ({ cnt; _ } as st) ->
      let ({ v; vids; _ } as env') = f env in
      let vids', cnt' =
        if Map.mem vids v then (vids, cnt)
        else (Map.add_exn vids ~key:v ~data:cnt, cnt + 1)
      in
      m { env' with vids = vids' } { st with cnt = cnt' }

    let get () : state t = fun _ st -> (st, st)
    let get_vid v : int t = fun { vids; _ } st -> (Map.find_exn vids v, st)

    let get_sid s : int t =
     fun _ ({ sids; _ } as st) -> (Map.find_exn sids s, st)

    let set_s s : unit t =
     fun _ ({ sids; cnt; _ } as st) ->
      let sids', cnt' =
        if Map.mem sids s then (sids, cnt)
        else (Map.add_exn sids ~key:s ~data:cnt, cnt + 1)
      in
      ((), { st with s; sids = sids'; cnt = cnt' })

    let set_cache f : unit t =
     fun _ ({ c; _ } as st) -> ((), { st with c = f c })

    let run (m : 'a t) =
      let empty_v = Set.empty (module V_key) in
      let empty_s = Set.empty (module Sigma) in
      m
        { v = empty_v; vids = Map.singleton (module V) empty_v 0 }
        {
          c = Map.empty (module Cache_key);
          s = empty_s;
          sids = Map.singleton (module S) empty_s 1;
          cnt = 2;
        }
  end

  include T
  include Monad.Make (T)
end

(** Truncates the stack to keep only the first k frames *)
let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

(** Checks if `sigma_child` is a prefix of `sigma_parent` *)
let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

(** Generates all matching stitched stacks per paper Section 4.2 *)
let suffixes l sigma s =
  s
  |> Set.filter_map
       (module Sigma)
       ~f:(function
         | l' :: sigma_sigma' when l = l' && starts_with sigma_sigma' sigma ->
             Some sigma_sigma'
         | _ -> None)
  |> Set.elements

(** max recursion depth ever reached by execution *)
let max_d = ref 0

(** Debug helper to log V IDs *)
let log_vids ?(size = false) ?(sort = false) vids =
  vids |> Map.to_alist |> fun vids ->
  (if not sort then vids
   else
     List.sort vids ~compare:(fun (_, id1) (_, id2) -> Int.descending id1 id2))
  |> List.iter ~f:(fun (key, data) ->
         if size then debug (fun m -> m "%d -> %d\n" (Set.length key) data)
         else debug (fun m -> m "%a -> %d\n" V.pp key data))

(** Debug helper to log S IDs *)
let log_sids ?(size = false) =
  Map.iteri ~f:(fun ~key ~data ->
      if size then debug (fun m -> m "%d -> %d\n" (Set.length key) data)
      else debug (fun m -> m "%a -> %d\n" S.pp key data))

(** A result containing both true and false *)
let bool_tf_res = Set.of_list (module Res_key) [ BoolAtom true; BoolAtom false ]

(** Generates all combinations of a binary int arithmetic
    operation over analysis results *)
let all_combs_int r1 r2 op =
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          (* Only performs basic simplications; basic precision *)
          | Atom.IntAtom b1, Atom.IntAtom b2 -> Set.add acc (IntAtom (op b1 b2))
          | _ -> Set.add acc IntAnyAtom))

(** Generates all combinations of a binary bool operation
    over analysis results *)
let all_combs_bool r1 r2 op =
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | Atom.BoolAtom b1, Atom.BoolAtom b2 ->
              Set.add acc (BoolAtom (op b1 b2))
          | _ -> Set.union acc bool_tf_res))

(** Generates all combinations of a binary int comparison
    operation over analysis results *)
let all_combs_bool' r1 r2 op =
  Set.fold r1 ~init:empty_res ~f:(fun acc a1 ->
      Set.fold r2 ~init:acc ~f:(fun acc a2 ->
          match (a1, a2) with
          | Atom.IntAtom i1, Atom.IntAtom i2 ->
              Set.add acc (BoolAtom (op i1 i2))
          | _ -> Set.union acc bool_tf_res))
