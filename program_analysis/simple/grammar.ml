open Core
open Interp.Ast

module S_key = struct
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

module V_key = struct
  module T = struct
    type lstate = int * sigma * string [@@deriving compare, sexp, hash]

    let show_lstate (l, sigma, s) =
      Format.sprintf "(%d, %s, %s)" l (S_key.show sigma) s

    let pp_lstate fmt lst = Format.fprintf fmt "%s" (show_lstate lst)

    type estate = expr * sigma * string [@@deriving compare, sexp, hash]

    let show_estate (e, sigma, s) =
      Format.asprintf "(%a, %s, %s)" Interp.Ast.pp_expr e (S_key.show sigma) s

    let pp_estate fmt est = Format.fprintf fmt "%s" (show_estate est)

    type t = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, hash]

    let show (k : t) =
      match k with
      | Lstate st -> Format.asprintf "%a" pp_lstate st
      | Estate st -> Format.asprintf "%a" pp_estate st
  end

  include T
  include Comparable.Make (T)
end

module Cache_key = struct
  module T = struct
    type t = expr * sigma * string * string [@@deriving compare, sexp, hash]
  end

  include T
  include Comparable.Make (T)
end

module V = struct
  module T = struct
    type t = Set.M(V_key).t [@@deriving compare, sexp]

    let show (v : t) =
      v |> Set.to_list |> List.map ~f:V_key.show |> String.concat ~sep:", "
      |> Format.sprintf "{%s}"
  end

  include T
  include Comparable.Make (T)
end

module S = struct
  module T = struct
    type t = Set.M(S_key).t [@@deriving compare, sexp]

    let show (s : t) =
      s |> Set.to_list |> List.map ~f:S_key.show |> String.concat ~sep:", "
      |> Format.sprintf "{%s}"
  end

  include T
  include Comparable.Make (T)
end

module Freq_key = struct
  module T = struct
    type t = expr * sigma * string * string [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

open Core
open Interp.Ast

module rec Atom : sig
  type t =
    | IntAnyAtom
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of expr * int * sigma
    | LStubAtom of (int * sigma)
    | EStubAtom of (expr * sigma)
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving compare, sexp]
end = struct
  type t =
    | IntAnyAtom
    | IntAtom of int
    | BoolAtom of bool
    | FunAtom of expr * int * sigma
    | LStubAtom of (int * sigma)
    | EStubAtom of (expr * sigma)
    | RecAtom of (ident * Res.t) list
    | ProjAtom of Res.t * ident
    | InspAtom of ident * Res.t
    | AssertAtom of ident * Res.t * res_val_fv
  [@@deriving compare, sexp]
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

and Res : sig
  type t = Set.M(Res_key).t [@@deriving compare, sexp]
end = struct
  type t = Set.M(Res_key).t [@@deriving compare, sexp]
end

type pi = (Res.t * bool) option [@@deriving compare]

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
let unwrap_res = Set.elements
