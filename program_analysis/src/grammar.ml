open Core
open Interpreter.Ast

module State = struct
  module T = struct
    type lstate = int * sigma [@@deriving compare, sexp]
    type estate = expr * sigma [@@deriving compare, sexp]

    type state = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp]

    type t = state * int [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

type path_cond = expr * bool [@@deriving compare, sexp]

type op =
  | PlusOp of res * res
  | MinusOp of res * res
  | EqualOp of res * res
  | AndOp of res * res
  | OrOp of res * res
  | NotOp of res

and atom =
  | IntAtom of int
  | BoolAtom of bool
  | FunAtom of expr * int * sigma
  | OpAtom of op
  | ResAtom of res
  | LabelResAtom of res * State.lstate
  | ExprResAtom of res * State.estate
  | LabelStubAtom of State.lstate
  | ExprStubAtom of State.estate
  | PathCondAtom of path_cond * atom

and res = atom list [@@deriving compare, sexp]

(* used to accumulate disjuncts when stitching stacks at Var Non-Local *)
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

module Maybe_int = struct
  module T = struct
    type t = DefInt of int | AnyInt [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

module Maybe_bool = struct
  module T = struct
    type t = DefBool of bool | AnyBool [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end
