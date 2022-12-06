val name : string

module Ast : sig
  type ident = Ddeast.ident = Ident of string

  type lexpr = expr * int

  and expr =
    | Int of int
    | Var of ident
    | Bool of bool
    | Function of ident * lexpr
    | Appl of lexpr * lexpr
    | Plus of lexpr * lexpr
    | Minus of lexpr * lexpr
    | Equal of lexpr * lexpr
    | And of lexpr * lexpr
    | Or of lexpr * lexpr
    | Not of lexpr
    | If of lexpr * lexpr * lexpr
    | Let of ident * lexpr * lexpr

  type fbtype = Ddeast.fbtype = TArrow of fbtype * fbtype | TVar of string

  val show_lexpr : lexpr -> string
  val pp_lexpr : Format.formatter -> lexpr -> unit [@@ocaml.toplevel_printer]
  val show_fbtype : fbtype -> string
  val pp_fbtype : Format.formatter -> fbtype -> unit [@@ocaml.toplevel_printer]
end

module Parser : sig
  type token

  val main : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Ast.lexpr
end

module Lexer : sig
  val token : Lexing.lexbuf -> Parser.token
end

module Typechecker : sig
  (* This exception is used to allow a language to dynamically signal that it *)
  (* does not have a typechecker.  If it is raised, it should be raised by a *)
  (* Typechecker module's typecheck function. *)
  exception TypecheckerNotImplementedException

  val typecheck : Ast.lexpr -> Ast.fbtype
  val typecheck_default_enabled : bool
end

module Pp : sig
  val show_lexpr : Ast.lexpr -> string
  val pp_lexpr : Format.formatter -> Ast.lexpr -> unit
  val show_fbtype : Ast.fbtype -> string
  val pp_fbtype : Format.formatter -> Ast.fbtype -> unit
end

module Interpreter : sig
  val eval : bool -> Ast.lexpr -> Ast.lexpr
end

module Options : sig
  val options : (Arg.key * Arg.spec * Arg.doc) list
end

module Version : sig
  val version : string
  val build_date : string
end
