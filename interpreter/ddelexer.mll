{
  [@@@coverage off]
  open Ddeparser;;
}

let blank = [' ' '\t' '\n' '\r']
let decimal_literal = ['0'-'9']+
let lowercase = ['a'-'z' '\223'-'\246' '\248'-'\255' '_']
let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']

rule token = parse
| "(*" ([^'*']|('*'[^')']))* ("*)"|"**)")
    {token lexbuf} (* Ignore comments *)
| blank+               { token lexbuf }
| "and"                { AND }
| "or"                 { OR }
| "not"                { NOT }
| "fun"                { FUNCTION }
| "function"           { FUNCTION }
| "if"                 { IF }
| "then"               { THEN }
| "else"               { ELSE }
| "let"                { LET }
| "in"                 { IN }
| "->"                 { GOESTO }
| "false"              { BOOL false }
| "true"               { BOOL true }
| ";;"                 { EOEX }
| '+'                  { PLUS }
| '-'                  { MINUS }
| '='                  { EQUAL }
| '('                  { LPAREN }
| ')'                  { RPAREN }
| decimal_literal      { INT (int_of_string(Lexing.lexeme lexbuf)) }
| lowercase identchar* { IDENT (Lexing.lexeme lexbuf) }
| eof                  { raise Exit }

{}
