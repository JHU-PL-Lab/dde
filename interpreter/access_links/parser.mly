%{

[@@@coverage off]
open Ast;;

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
%token GE
%token GOESTO
%token GT
%token <string> IDENT
%token IN
%token IF
%token <int> INT
// %token LBRACE
%token LE
%token LET
// %token LETASSERT
%token LPAREN
%token LT
%token MINUS
%token MULT
%token NOT
%token OR
%token PLUS
// %token PROJECT
// %token RBRACE
%token RPAREN
// %token SEP
%token THEN

/*
 * Precedences and associativities.  Lower precedences come first.
 */
%right prec_let                         /* let x = ... in ... */
%right prec_fun                         /* function declaration */
%right prec_if                          /* if ... then ... else */
// %right OR                               /* or */
// %right AND                              /* and */
%left EQUAL                             /* = */
// %left GE GT LE LT                       /* >= > <= < */
%left PLUS MINUS                        /* + - */
// %left MULT                              /* * */
// %right NOT                              /* not e */

/*
 * The entry point.
 */
%start main
%type <expr> main

%%

main:
  expr EOEX { $1 }
;

expr:
  | appl_expr
      { $1 }
  | expr PLUS expr
      { build_plus $1 $3 }
  | expr MINUS expr
      { build_minus $1 $3 }
  | expr MULT expr
      { build_mult $1 $3 }
  | expr AND expr
      { build_and $1 $3 }
  | expr OR expr
      { build_or $1 $3 }
  | expr GE expr
      { build_ge $1 $3 }
  | expr GT expr
      { build_gt $1 $3 }
  | expr LE expr
      { build_le $1 $3 }
  | expr LT expr
      { build_lt $1 $3 }
  | NOT expr
      { build_not $2 }
  | expr EQUAL expr
      { build_eq $1 $3 }
  | FUNCTION ident_decl GOESTO expr %prec prec_fun
      { build_fun $2 $4 }
  | LET ident_decl EQUAL expr IN expr %prec prec_let
      { build_let $2 $4 $6 }
//   | LETASSERT ident_decl EQUAL expr IN expr %prec prec_let
//      { build_letassert $2 $4 $6 }
  | IF expr THEN expr ELSE expr %prec prec_if
      { build_if $2 $4 $6 }
//   | LBRACE separated_list(SEP, record_entry) RBRACE
//       { build_record $2 }
//   | expr PROJECT IDENT
//       { build_projection $1 $3 }
//   | IDENT IN expr
//       { build_inspection $1 $3 }
;

// record_entry:
//     ident_decl EQUAL expr
//       { ($1, $3) }

appl_expr:
  | negatable_expr
      { $1 }
  | appl_expr simple_expr
      { build_app $1 $2 }
;

negatable_expr:
  | MINUS INT
      { build_int (-$2) }
  | simple_expr
      { $1 }
;

simple_expr:
  | INT
      { build_int $1 }
  | BOOL
      { build_bool $1 }
  | ident_usage
      { $1 }
  | LPAREN expr RPAREN
      { $2 }
;

ident_usage:
    ident_decl
      { build_var $1 }
;

ident_decl:
    IDENT
      { Ident $1 }
;

%%
