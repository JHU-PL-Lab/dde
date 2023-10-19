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
%token LBRACE
%token LE
%token LET
%token LETASSERT
%token LPAREN
%token LT
%token MINUS
%token MULT
%token NOT
%token OR
%token PLUS
%token PROJECT
%token RBRACE
%token RPAREN
%token SEP
%token THEN

/*
 * Precedences and associativities.  Lower precedences come first.
 */
%right prec_let                         /* let x = ... in ... */
%right prec_fun                         /* function declaration */
%right prec_if                          /* if ... then ... else */
%right OR                               /* or */
%right AND                              /* and */
%left EQUAL                             /* = */
%left GE GT LE LT                       /* >= > <= < */
%left PLUS MINUS                        /* + - */
%left MULT                              /* * */
%right NOT                              /* not e */

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
      { mk_dplus $1 $3 }
  | expr MINUS expr
      { mk_dminus $1 $3 }
  | expr MULT expr
      { mk_dmult $1 $3 }
  | expr AND expr
      { mk_dand $1 $3 }
  | expr OR expr
      { mk_dor $1 $3 }
  | expr GE expr
      { mk_dge $1 $3 }
  | expr GT expr
      { mk_dgt $1 $3 }
  | expr LE expr
      { mk_dle $1 $3 }
  | expr LT expr
      { mk_dlt $1 $3 }
  | NOT expr
      { mk_dnot $2 }
  | expr EQUAL expr
      { mk_deq $1 $3 }
  | FUNCTION ident_decl GOESTO expr %prec prec_fun
      { mk_dfun $2 $4 }
  | LET ident_decl EQUAL expr IN expr %prec prec_let
      { mk_dlet $2 $4 $6 }
  | LETASSERT ident_decl EQUAL expr IN expr %prec prec_let
     { mk_dletassert $2 $4 $6 }
  | IF expr THEN expr ELSE expr %prec prec_if
      { mk_dif $2 $4 $6 }
  | LBRACE separated_list(SEP, record_entry) RBRACE
      { mk_drec $2 }
  | expr PROJECT IDENT
      { mk_dproj $1 (Ident $3) }
  | IDENT IN expr
      { mk_dinsp (Ident $1) $3 }
;

record_entry:
    ident_decl EQUAL expr
      { ($1, $3) }

appl_expr:
  | negatable_expr
      { $1 }
  | appl_expr simple_expr
      { mk_dapp $1 $2 }
;

negatable_expr:
  | MINUS INT
      { mk_dint (-$2) }
  | simple_expr
      { $1 }
;

simple_expr:
  | INT
      { mk_dint $1 }
  | BOOL
      { mk_dbool $1 }
  | ident_usage
      { $1 }
  | LPAREN expr RPAREN
      { $2 }
;

ident_usage:
    ident_decl
      { mk_dvar $1 }
;

ident_decl:
    IDENT
      { Ident $1 }
;

%%
