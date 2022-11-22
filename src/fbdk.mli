val name : string

module Ast : sig
  type ident = Ddeast.ident = Ident of string

  type expr = Ddeast.expr =
    | Int of int * int
    | Var of ident * int
    | Bool of bool * int
    | Function of ident * expr * int
    | Appl of expr * expr * int
    | Plus of expr * expr * int
    | Minus of expr * expr * int
    | Equal of expr * expr * int
    | And of expr * expr * int
    | Or of expr * expr * int
    | Not of expr * int
    | If of expr * expr * expr * int
    | Let of ident * expr * expr * int

  type fbtype = Ddeast.fbtype = TArrow of fbtype * fbtype | TVar of string

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

module Pp : sig
  val show_expr : Ast.expr -> string
  val pp_expr : Format.formatter -> Ast.expr -> unit
  val show_fbtype : Ast.fbtype -> string
  val pp_fbtype : Format.formatter -> Ast.fbtype -> unit
end

module Interpreter : sig
  val eval : Ast.expr -> Ast.expr
end

module Options : sig
  val options : (Arg.key * Arg.spec * Arg.doc) list
end

module Version : sig
  val version : string
  val build_date : string
end