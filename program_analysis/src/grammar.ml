open Core
open Interpreter.Ast

module State = struct
  module T = struct
    type lstate = int * sigma
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type estate = expr * sigma
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type state = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, hash, show { with_path = false }]

    type t = state * int
    [@@deriving compare, sexp, hash, show { with_path = false }]
  end

  include T
  include Comparable.Make (T)
end

type op =
  | PlusOp of res * res
  | MinusOp of res * res
  | MultOp of res * res
  | EqualOp of res * res
  | AndOp of res * res
  | OrOp of res * res
  | GeOp of res * res
  | GtOp of res * res
  | LeOp of res * res
  | LtOp of res * res
  | NotOp of res

and atom =
  | IntAtom of int
  | BoolAtom of bool
  | FunAtom of expr * int * sigma
  | OpAtom of op
  | LabelResAtom of res * State.lstate
  | ExprResAtom of res * State.estate
  | LabelStubAtom of State.lstate
  | ExprStubAtom of State.estate
  | PathCondAtom of path_cond * res
  | RecordAtom of (ident * res) list
  | ProjectionAtom of res * ident
  | InspectionAtom of ident * res
  | AssertAtom of ident * res * Interpreter.Ast.result_value_fv

and res = atom list

and path_cond = res * bool
[@@deriving hash, sexp, compare, show { with_path = false }]

type pi = (atom list * bool) option [@@deriving hash, sexp, compare]

module CacheKey = struct
  module T = struct
    type t = expr * sigma * pi [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

(* used to accumulate disjuncts when stitching stacks *)
module Choice = struct
  module T = struct
    type t = atom [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module PathChoice = struct
  module T = struct
    type t = path_cond * atom [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Maybe_prim = struct
  module T = struct
    type t = DefInt of int | DefBool of bool | Any [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end
