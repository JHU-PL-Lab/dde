open Core
open Interpreter.Ast

module SKey = struct
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

module NewSt = struct
  module T = struct
    type lstate =
      int
      * sigma
      * ((SKey.t, (SKey.comparator_witness[@compare.ignore])) Set.t
        [@sexp.opaque] [@show.opaque] [@hash.ignore])
    [@@deriving compare, sexp, hash]

    let show_set s =
      s |> Set.to_list |> List.map ~f:show_sigma |> String.concat ~sep:", "

    let show_lstate (l, sigma, s) =
      Format.sprintf "(%d, %s, {%s})" l (show_sigma sigma) (show_set s)

    let pp_lstate fmt lst = Format.fprintf fmt "%s" (show_lstate lst)

    type estate =
      expr
      * sigma
      * ((SKey.t, (SKey.comparator_witness[@compare.ignore])) Set.t
        [@sexp.opaque] [@show.opaque] [@hash.ignore])
    [@@deriving compare, sexp, hash]

    let show_estate (e, sigma, s) =
      Format.asprintf "(%a, %s, {%s})" Interpreter.Ast.pp_expr e
        (show_sigma sigma) (show_set s)

    let pp_estate fmt est = Format.fprintf fmt "%s" (show_estate est)

    type t = Lstate of lstate | Estate of estate
    [@@deriving compare, sexp, show { with_path = false }, hash]
  end

  include T
  include Comparable.Make (T)
end

module Cache_key = struct
  module T = struct
    (* type t = expr * sigma [@@deriving hash, sexp, compare] *)
    type t =
      expr
      * sigma
      * ((NewSt.t, (NewSt.comparator_witness[@compare.ignore])) Set.t
        [@sexp.opaque])
    [@@deriving compare, sexp]

    let hash = Hashtbl.hash
  end

  include T
  include Comparable.Make (T)
end

open Core
open Interpreter.Ast

type atom =
  | IntAllAtom
  | IntAtom of int
  | BoolAtom of bool
  | FunAtom of expr * int * sigma
  | LabelStubAtom of (int * sigma)
  | ExprStubAtom of (expr * sigma)
  | RecordAtom of (ident * res) list
  | ProjectionAtom of res * ident
  | InspectionAtom of ident * res
  | AssertAtom of ident * res * res_val_fv

and res = atom list [@@deriving hash, sexp, compare, show { with_path = false }]

type pi = (atom list * bool) option
[@@deriving hash, sexp, compare, show { with_path = false }]

module Let_syntax = struct
  let return r = (r, Set.empty (module SKey))

  let bind (r, s) ~f =
    let r', s' = f (r, s) in
    (r', Set.union s s')

  let map (r, s) ~f = return (f (r, s))
  let ( >>= ) t f = bind t ~f
  let ( >>| ) t f = map t ~f
end

(* used to accumulate disjuncts when stitching stacks *)
module Choice = struct
  module T = struct
    type t = atom [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

(* module PathChoice = struct
     module T = struct
       type t = path_cond * atom [@@deriving compare, sexp]
     end

     include T
     include Comparable.Make (T)
   end *)

module AtomKey = struct
  module T = struct
    type t = atom [@@deriving hash, sexp, compare]
  end

  include T
  include Comparable.Make (T)
end

module ResKey = struct
  module T = struct
    type t = res [@@deriving hash, sexp, compare]
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
