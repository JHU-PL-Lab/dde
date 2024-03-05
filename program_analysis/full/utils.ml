(** Utility data structures and functions *)

open Core
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
      Format.fprintf fmt "(%a, %a, %d)" Expr.pp e Sigma.pp sigma sid

    let show_estate (e, sigma, sid) =
      Format.asprintf "(%a, %s, %d)" Expr.pp e (Sigma.show sigma) sid

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

(** Value atom per paper Fig. 16 *)
module rec Atom : sig
  type t =
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of Expr.t * sigma
    | LResAtom of Res.t * St.lstate (* cycle start (applications) *)
    | EResAtom of Res.t * St.estate (* cycle start (variables) *)
    | LStubAtom of St.lstate (* cycle end (applications) *)
    | EStubAtom of St.estate (* cycle end (variables) *)
    | PathCondAtom of (Res.t * bool) * Res.t
    | PlusAtom of Res.t * Res.t
    | MinusAtom of Res.t * Res.t
    | MultAtom of Res.t * Res.t
    | EqAtom of Res.t * Res.t
    | GeAtom of Res.t * Res.t
    | GtAtom of Res.t * Res.t
    | LeAtom of Res.t * Res.t
    | LtAtom of Res.t * Res.t
    | AndAtom of Res.t * Res.t
    | OrAtom of Res.t * Res.t
    | NotAtom of Res.t
    | RecAtom of (Ident.t * Res.t) list
    | ProjAtom of Res.t * Ident.t
    | InspAtom of Ident.t * Res.t
    | AssertAtom of Ident.t * Res.t * Res_fv.t
  [@@deriving sexp, compare]

  val pp : Format.formatter -> t -> unit
end = struct
  type t =
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of Expr.t * sigma
    | LResAtom of Res.t * St.lstate
    | EResAtom of Res.t * St.estate
    | LStubAtom of St.lstate
    | EStubAtom of St.estate
    | PathCondAtom of (Res.t * bool) * Res.t
    | PlusAtom of Res.t * Res.t
    | MinusAtom of Res.t * Res.t
    | MultAtom of Res.t * Res.t
    | EqAtom of Res.t * Res.t
    | GeAtom of Res.t * Res.t
    | GtAtom of Res.t * Res.t
    | LeAtom of Res.t * Res.t
    | LtAtom of Res.t * Res.t
    | AndAtom of Res.t * Res.t
    | OrAtom of Res.t * Res.t
    | NotAtom of Res.t
    | RecAtom of (Ident.t * Res.t) list
    | ProjAtom of Res.t * Ident.t
    | InspAtom of Ident.t * Res.t
    | AssertAtom of Ident.t * Res.t * Res_fv.t
  [@@deriving sexp, compare]

  let rec pp_record fmt = function
    | [] -> ()
    | [ (Ident.Ident x, v) ] -> Format.fprintf fmt "%s = %a" x Res.pp v
    | (Ident x, v) :: rest ->
        Format.fprintf fmt "%s = %a; %a" x Res.pp v pp_record rest

  and pp fmt = function
    | IntAtom x -> ff fmt "%d" x
    | BoolAtom b -> ff fmt "%b" b
    | FunAtom (f, _) -> Expr.pp fmt f
    | LResAtom (choices, _) -> ff fmt "%a" Res.pp choices
    (* | LResAtom (choices, _) -> ff fmt "%a#" Res.pp choices *)
    | EResAtom (choices, _) -> ff fmt "%a" Res.pp choices
    (* | EResAtom (choices, _) -> ff fmt "%a$" Res.pp choices *)
    | LStubAtom _ -> ff fmt "stub"
    | EStubAtom _ -> ff fmt "stub"
    | PlusAtom (r1, r2) -> ff fmt "(%a + %a)" Res.pp r1 Res.pp r2
    | MinusAtom (r1, r2) -> ff fmt "(%a - %a)" Res.pp r1 Res.pp r2
    | MultAtom (r1, r2) -> ff fmt "(%a * %a)" Res.pp r1 Res.pp r2
    | EqAtom (r1, r2) -> ff fmt "(%a = %a)" Res.pp r1 Res.pp r2
    | AndAtom (r1, r2) -> ff fmt "(%a and %a)" Res.pp r1 Res.pp r2
    | OrAtom (r1, r2) -> ff fmt "(%a or %a)" Res.pp r1 Res.pp r2
    | GeAtom (r1, r2) -> ff fmt "(%a >= %a)" Res.pp r1 Res.pp r2
    | GtAtom (r1, r2) -> ff fmt "(%a > %a)" Res.pp r1 Res.pp r2
    | LeAtom (r1, r2) -> ff fmt "(%a <= %a)" Res.pp r1 Res.pp r2
    | LtAtom (r1, r2) -> ff fmt "(%a < %a)" Res.pp r1 Res.pp r2
    | NotAtom r1 -> ff fmt "(not %a)" Res.pp r1
    | PathCondAtom (_, r) -> ff fmt "%a" Res.pp r
    (* | PathCondAtom ((r, b), r') -> ff fmt "(%a = %b ⊩ %a)" Res.pp r b Res.pp r' *)
    | RecAtom entries ->
        ff fmt
          (if List.is_empty entries then "{%a}" else "{ %a }")
          pp_record entries
    | ProjAtom (r, Ident s) -> ff fmt "(%a.%s)" Res.pp r s
    | InspAtom (Ident s, r) -> ff fmt "(%s in %a)" s Res.pp r
    | AssertAtom (_, r, _) -> ff fmt "%a" Res.pp r
end

(** Value result per paper Fig. 16 *)
and Res : sig
  type t = Atom.t list [@@deriving sexp, compare]

  val pp : Format.formatter -> t -> unit
  val show : t -> string
  val ( = ) : t -> t -> bool
end = struct
  module T = struct
    type t = Atom.t list [@@deriving sexp, compare]

    let rec pp_aux fmt = function
      | [] -> ()
      | [ a ] -> ff fmt "%a" Atom.pp a
      | a :: _as -> ff fmt "(%a | %a)" Atom.pp a pp_aux _as

    and pp fmt r = if List.is_empty r then ff fmt "#" else ff fmt "%a" pp_aux r

    let show (r : t) = Format.asprintf "%a" pp r
  end

  include T
  include Comparable.Make (T)
end

(* Path condition per paper Fig. 16 *)
type pi = (Res.t * bool) option
[@@deriving sexp, compare, show { with_path = false }]

module Res_key : sig
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

module Cache_key = struct
  module T = struct
    type lkey = int * sigma * int * int * pi [@@deriving compare, sexp]
    type ekey = Expr.t * sigma * int * int * pi [@@deriving compare, sexp]
    type t = Lkey of lkey | Ekey of ekey [@@deriving compare, sexp]

    let pp_lkey fmt (l, sigma, vid, sid, pi) =
      Format.fprintf fmt "(%d, %a, %d, %d)" l Sigma.pp sigma vid sid
    (* pp_pi pi *)

    let show_lkey (l, sigma, vid, sid, pi) =
      Format.asprintf "(%d, %a, %d, %d)" l Sigma.pp sigma vid sid
    (* (show_pi pi) *)

    let pp_ekey fmt (expr, sigma, vid, sid, pi) =
      Format.fprintf fmt "(%a, %a, %d, %d)" Expr.pp expr Sigma.pp sigma vid sid
    (* pp_pi pi *)

    let show_ekey (expr, sigma, vid, sid, pi) =
      Format.asprintf "(%a, %a, %d, %d)" Expr.pp expr Sigma.pp sigma vid sid
    (* (show_pi pi) *)

    let pp fmt = function
      | Lkey lkey -> pp_lkey fmt lkey
      | Ekey ekey -> pp_ekey fmt ekey

    let show = function
      | Lkey lkey -> show_lkey lkey
      | Ekey ekey -> show_ekey ekey

    (* type lkey = int * sigma * int * pi [@@deriving compare, sexp]
       type ekey = expr * sigma * int * pi [@@deriving compare, sexp]
       type t = Lkey of lkey | Ekey of ekey [@@deriving compare, sexp]

       let pp_lkey fmt (l, sigma, sid, pi) =
         Format.fprintf fmt "(%d, %a, %d, %a)" l Sigma.pp sigma sid pp_pi pi

       let show_lkey (l, sigma, sid, pi) =
         Format.asprintf "(%d, %a, %d, %s)" l Sigma.pp sigma sid (show_pi pi)

       let pp_ekey fmt (expr, sigma, sid, pi) =
         Format.fprintf fmt "(%a, %a, %d, %a)" Expr.pp expr Sigma.pp
           sigma sid pp_pi pi

       let show_ekey (expr, sigma, sid, pi) =
         Format.asprintf "(%a, %a, %d, %s)" Expr.pp expr Sigma.pp sigma
           sid (show_pi pi)

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

(** Reader-State monad threaded through the full analysis *)
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

(** Max recursion depth ever reached by execution *)
let max_d = ref 0
