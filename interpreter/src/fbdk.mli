val name : string

module Ast : sig
  type ident = Ast.ident = Ident of string

  type expr =
    | Int of int
    | Bool of bool
    | Function of ident * expr * int
    | Var of ident * int
    | Appl of expr * expr * int
    | Plus of expr * expr
    | Minus of expr * expr
    | Equal of expr * expr
    | And of expr * expr
    | Or of expr * expr
    | Ge of expr * expr
    | Gt of expr * expr
    | Le of expr * expr
    | Lt of expr * expr
    | Not of expr
    | If of expr * expr * expr * int
    | Let of ident * expr * expr * int
    | LetAssert of ident * expr * expr
    | Record of (ident * expr) list
    | Projection of expr * ident
    | Inspection of ident * expr

  type sigma = int list

  type op_result_value =
    | PlusOp of result_value * result_value
    | MinusOp of result_value * result_value
    | EqualOp of result_value * result_value
    | AndOp of result_value * result_value
    | OrOp of result_value * result_value
    | GeOp of result_value * result_value
    | GtOp of result_value * result_value
    | LeOp of result_value * result_value
    | LtOp of result_value * result_value
    | NotOp of result_value

  and result_value =
    | IntResult of int
    | BoolResult of bool
    | FunResult of { f : expr; l : int; sigma : int list }
    | OpResult of op_result_value
    | RecordResult of (ident * result_value) list
    | ProjectionResult of result_value * ident
    | InspectionResult of ident * result_value

  type op_result_value_fv =
    | PlusOpFv of result_value_fv
    | MinusOpFv of result_value_fv
    | EqOpFv of result_value_fv
    | AndOpFv of result_value_fv * result_value_fv
    | OrOpFv of result_value_fv * result_value_fv
    | GeOpFv of result_value_fv
    | GtOpFv of result_value_fv
    | LeOpFv of result_value_fv
    | LtOpFv of result_value_fv
    | NotOpFv

  and result_value_fv =
    | IntResultFv of int
    | BoolResultFv of bool
    | VarResultFv
    | OpResultFv of op_result_value_fv
    | FunResultFv
    | RecordResultFv
    | ProjectionResultFv
    | InspectionResultFv

  type fbtype = Ast.fbtype = TArrow of fbtype * fbtype | TVar of string

  val show_expr : expr -> string
  val pp_expr : Format.formatter -> expr -> unit [@@ocaml.toplevel_printer]
  val show_fbtype : fbtype -> string
  val pp_fbtype : Format.formatter -> fbtype -> unit [@@ocaml.toplevel_printer]
end

module Parser : sig
  type token

  val main : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Ast.expr
end

module Lexer : sig
  val token : Lexing.lexbuf -> Parser.token
end

module Typechecker : sig
  (* This exception is used to allow a language to dynamically signal that it *)
  (* does not have a typechecker.  If it is raised, it should be raised by a *)
  (* Typechecker module's typecheck function. *)
  exception TypecheckerNotImplementedException

  val typecheck : Ast.expr -> Ast.fbtype
  val typecheck_default_enabled : bool
end

module Interpreter : sig
  val eval :
    Ast.expr -> is_debug_mode:bool -> should_simplify:bool -> Ast.result_value
end

module Pp : sig
  val show_expr : Ast.expr -> string
  val pp_expr : Format.formatter -> Ast.expr -> unit
  val pp_result_value : Format.formatter -> Ast.result_value -> unit
  val show_fbtype : Ast.fbtype -> string
  val pp_fbtype : Format.formatter -> Ast.fbtype -> unit
end

module Options : sig
  val options : (Arg.key * Arg.spec * Arg.doc) list
end
