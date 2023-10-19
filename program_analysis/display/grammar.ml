open Core
open Dinterp

module DS_key = struct
  module T = struct
    type t = Interp.d [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

type s =
  ((DS_key.t, (DS_key.comparator_witness[@compare.ignore])) Set.t[@sexp.opaque])
[@@deriving compare, sexp]

module DV_key = struct
  module T = struct
    type t = int * Interp.d * s [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

type v = (DV_key.t, (DV_key.comparator_witness[@compare.ignore])) Set.t

module rec DAtom : sig
  type t =
    | DIntAnyAtom
    | DIntAtom of int
    | DBoolAtom of bool
    | DFunAtom of Ast.expr * Interp.d
    (* | DPlusAtom of DRes.t * DRes.t
       | DMinusAtom of DRes.t * DRes.t
       | DMultAtom of DRes.t * DRes.t
       | DEqAtom of DRes.t * DRes.t
       | DGeAtom of DRes.t * DRes.t
       | DGtAtom of DRes.t * DRes.t
       | DLeAtom of DRes.t * DRes.t
       | DLtAtom of DRes.t * DRes.t
       | DAndAtom of DRes.t * DRes.t
       | DOrAtom of DRes.t * DRes.t
       | DNotAtom of DRes.t *)
    | DRecAtom of (Ast.ident * DRes.t) list
    | DProjAtom of DRes.t * Ast.ident
    | DInspAtom of Ast.ident * DRes.t
    | DStubAtom of (int * Interp.d * s)
  [@@deriving compare, sexp]
end = struct
  type t =
    | DIntAnyAtom
    | DIntAtom of int
    | DBoolAtom of bool
    | DFunAtom of Ast.expr * Interp.d
    (* | DPlusAtom of DRes.t * DRes.t
       | DMinusAtom of DRes.t * DRes.t
       | DMultAtom of DRes.t * DRes.t
       | DEqAtom of DRes.t * DRes.t
       | DGeAtom of DRes.t * DRes.t
       | DGtAtom of DRes.t * DRes.t
       | DLeAtom of DRes.t * DRes.t
       | DLtAtom of DRes.t * DRes.t
       | DAndAtom of DRes.t * DRes.t
       | DOrAtom of DRes.t * DRes.t
       | DNotAtom of DRes.t *)
    | DRecAtom of (Ast.ident * DRes.t) list
    | DProjAtom of DRes.t * Ast.ident
    | DInspAtom of Ast.ident * DRes.t
    | DStubAtom of (int * Interp.d * s)
  [@@deriving compare, sexp]
end

and DRes_key : sig
  type t = DAtom.t [@@deriving compare, sexp]
  type comparator_witness

  val comparator : (t, comparator_witness) Comparator.t
end = struct
  module T = struct
    type t = DAtom.t [@@deriving compare, sexp]
  end

  include T
  include Comparable.Make (T)
end

and DRes : sig
  type t =
    ((DRes_key.t, (DRes_key.comparator_witness[@compare.ignore])) Set.t
    [@sexp.opaque])
  [@@deriving compare, sexp]
end = struct
  type t =
    ((DRes_key.t, (DRes_key.comparator_witness[@compare.ignore])) Set.t
    [@sexp.opaque])
  [@@deriving compare, sexp]
end
