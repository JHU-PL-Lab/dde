%{

[@@@coverage off]
open Ddeast;;

%}

/*
 * Tokens
 */

%token AND
%token <bool> BOOL
%token ELSE
%token EOEX
%token EQUAL
%token FUNCTION
%token GOESTO
%token <string> IDENT
%token IN
%token IF
%token <int> INT
%token LET
%token LPAREN
%token MINUS
%token NOT
%token OR
%token PLUS
%token RPAREN
%token THEN

/*
 * Precedences and associativities.  Lower precedences come first.
 */
%right prec_let                         /* let f x = ... in ... */
%right prec_fun                         /* function declaration */
%right prec_if                          /* if ... then ... else */
%right OR                               /* or */
%right AND                              /* and */
%left EQUAL                             /* = */
%left PLUS MINUS                        /* + - */
%right NOT                              /* not e */

/*
 * The entry point.
 */
%start main
%type <Ddeast.lexpr> main

%%

main:
  expr EOEX { $1 }
;

expr:
  | appl_expr
      { $1 }
  | expr PLUS expr
      { build_labeled_plus $1 $3 }
  | expr MINUS expr
      { build_labeled_minus $1 $3 }
  | expr AND expr
      { build_labeled_and $1 $3 }
  | expr OR expr
      { build_labeled_or $1 $3 }
  | NOT expr
      { build_labeled_not $2 }
  | expr EQUAL expr
      { build_labeled_equal $1 $3 }
  | FUNCTION ident_decl GOESTO expr %prec prec_fun
      { build_labeled_function $2 $4 }
  | LET ident_decl EQUAL expr IN expr %prec prec_let
      { build_labeled_let $2 $4 $6 }
  | IF expr THEN expr ELSE expr %prec prec_if
      { build_labeled_if $2 $4 $6 }
;

appl_expr:
  | negatable_expr
      { $1 }
  | appl_expr simple_expr
      { build_labeled_appl $1 $2 }
;

negatable_expr:
  | MINUS INT
      { build_labeled_int (-$2) }
  | simple_expr
      { $1 }
;

simple_expr:
  | INT
      { build_labeled_int $1 }
  | BOOL
      { build_labeled_bool $1 }
  | ident_usage
      { $1 }
  | LPAREN expr RPAREN
      { $2 }
;

ident_usage:
    ident_decl
      { build_labeled_var $1 }
;

ident_decl:
    IDENT
      { Ident $1 }
;

%%
