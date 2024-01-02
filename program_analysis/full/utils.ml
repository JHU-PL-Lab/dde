open Core
open Interp.Ast

let ff = Format.fprintf

module Sigma = struct
  module T = struct
    type t = sigma [@@deriving compare, sexp, show { with_path = false }, hash]
  end

  include T
  include Comparable.Make (T)
end

module St = struct
  module T = struct
    type lstate = int * sigma
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type estate = expr * sigma
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type t = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, hash, show { with_path = false }]
  end

  include T
  include Comparable.Make (T)
end

module S = struct
  module T = struct
    type t = Set.M(Sigma).t [@@deriving compare, sexp, hash]

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
    type lstate = int * sigma * int [@@deriving compare, sexp, hash]

    let pp_lstate fmt (l, sigma, sid) =
      Format.fprintf fmt "(%d, %a, %d)" l Sigma.pp sigma sid

    let show_lstate (l, sigma, sid) =
      Format.sprintf "(%d, %s, %d)" l (Sigma.show sigma) sid

    type estate = expr * sigma * int [@@deriving compare, sexp, hash]

    let pp_estate fmt (e, sigma, sid) =
      Format.fprintf fmt "(%a, %a, %d)" Interp.Pp.pp_expr e Sigma.pp sigma sid

    let show_estate (e, sigma, sid) =
      Format.asprintf "(%a, %s, %d)" Interp.Ast.pp_expr e (Sigma.show sigma) sid

    type t = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, hash]

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

module V = struct
  module T = struct
    type t = Set.M(V_key).t [@@deriving compare, sexp, hash]

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

module rec Atom : sig
  type t =
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of expr * int * sigma
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
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving hash, sexp, compare]

  val pp : Format.formatter -> t -> unit
end = struct
  type t =
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of expr * int * sigma
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
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving hash, sexp, compare]

  let rec pp_record fmt = function
    | [] -> ()
    | [ (Ident x, v) ] -> Format.fprintf fmt "%s = %a" x Res.pp v
    | (Ident x, v) :: rest ->
        Format.fprintf fmt "%s = %a; %a" x Res.pp v pp_record rest

  and pp fmt = function
    | IntAtom x -> ff fmt "%d" x
    | BoolAtom b -> ff fmt "%b" b
    | FunAtom (f, _, _) -> Interp.Pp.pp_expr fmt f
    | LResAtom (choices, _) -> ff fmt "%a" Res.pp choices
    | EResAtom (choices, _) -> ff fmt "%a" Res.pp choices
    | LStubAtom _ -> ff fmt "stub"
    | EStubAtom _ -> ff fmt "stub"
    (* | LResAtom (choices, (l, _)) -> ff fmt "(%a)^%d" Res.pp choices l
       | EResAtom (choices, (e, _)) ->
           ff fmt "(%a)^%a" Res.pp choices Interp.Pp.pp_expr e
       | LStubAtom (l, _) -> ff fmt "stub@%d" l
       | EStubAtom (e, _) -> ff fmt "(stub@%a)" Interp.Pp.pp_expr e *)
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
    (* | EquivStubAtom (s, l) ->
        ff fmt "{%s}[%d]"
          (s |> Set.elements
          |> List.map ~f:(fun st -> Format.sprintf "%s" (St.show st))
          |> String.concat ~sep:", ")
          l *)
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

and Res : sig
  type t = Atom.t list [@@deriving hash, sexp, compare]

  val pp : Format.formatter -> t -> unit
  val show : t -> string
end = struct
  type t = Atom.t list [@@deriving hash, sexp, compare]

  let rec pp_aux fmt = function
    | [] -> ()
    | [ a ] -> ff fmt "%a" Atom.pp a
    | a :: _as -> ff fmt "%a | %a" Atom.pp a pp_aux _as

  and pp fmt r = if List.is_empty r then ff fmt "#" else ff fmt "%a" pp_aux r

  let show (r : t) = Format.asprintf "%a" pp r
end

type pi = (Res.t * bool) option
[@@deriving hash, sexp, compare, show { with_path = false }]

module Res_key : sig
  type t = Atom.t [@@deriving hash, compare, sexp]
  type comparator_witness

  val comparator : (t, comparator_witness) Comparator.t
end = struct
  module T = struct
    type t = Atom.t [@@deriving hash, compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Cache_key = struct
  module T = struct
    type t = expr * sigma * int * int * pi [@@deriving hash, compare, sexp]

    let pp fmt (expr, sigma, vid, sid, pi) =
      Format.fprintf fmt "(%a, %a, %d, %d, %a)" Interp.Pp.pp_expr expr Sigma.pp
        sigma vid sid pp_pi pi

    let show (expr, sigma, vid, sid, pi) =
      Format.asprintf "(%a, %a, %d, %d, %s)" Interp.Pp.pp_expr expr Sigma.pp
        sigma vid sid (show_pi pi)
  end

  include T
  include Comparable.Make (T)
end

module Tmp_res_key = struct
  module T = struct
    type t = Res.t [@@deriving hash, compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Z3ExprKey = struct
  module T = struct
    open Z3

    type t = Expr.expr

    let compare = Expr.compare
    let sexp_of_t e = e |> Expr.ast_of_expr |> AST.to_sexpr |> Sexp.of_string
    let t_of_sexp s = failwith "unimplemented"
    let hash e = e |> Expr.ast_of_expr |> AST.hash
  end

  include T
  include Comparable.Make (T)
end

let empty_res = Set.empty (module Res_key)
let single_res = Set.singleton (module Res_key)

(** Reader-State monad threaded through the analysis *)
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

    let set_cache c : unit t = fun _ st -> ((), { st with c })
  end

  include T
  include Monad.Make (T)
end

let prune_sigma ?(k = 2) s = List.filteri s ~f:(fun i _ -> i < k)

let rec starts_with sigma_parent sigma_child =
  match (sigma_parent, sigma_child) with
  | _, [] -> true
  | [], _ -> false
  | l_parent :: ls_parent, l_child :: ls_child ->
      l_parent = l_child && starts_with ls_parent ls_child

let suffixes l sigma s =
  s
  |> Set.filter_map
       (module Sigma)
       ~f:(function
         | l' :: sigma_sigma' when l = l' && starts_with sigma_sigma' sigma ->
             Some sigma_sigma'
         | _ -> None)
  |> Set.elements
