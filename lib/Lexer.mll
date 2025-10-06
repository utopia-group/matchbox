{
  open Core
  open Parser

  exception ParseError of string

}

let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

rule tokens = parse
| [' ' '\t' '\n'] { tokens lexbuf }
| ['0'-'9']+ as i { INT (Int.of_string i) }
| "action" { ACTION }
| "else" { ELSE }
| "key" { KEY }
| "data" { DATA }
| "to" { TO }
| "o--" { MATCHSTICK }
| ">>" { COMPOSE }
| ":=" { ASSIGN }
| ";" { SEMICOLON }
| ":" { COLON }
| "," { COMMA }
| "*" { TIMES }
| "." { DOT }
| "[" { LSQUARE }
| "]" { RSQUARE }
| "(" { LPAREN }
| ")" { RPAREN }
| "{" { LBRACE }
| "}" { RBRACE }
| "delete" { DELETE }
| "ignore" { IGNORE }
| "true" { TRUE }
| "false" { FALSE }
| "filter" { FILTER }
| "rename" { RENAME }
| "tcam" { TCAM }
| "cam" { CAM }
| "lpm" { LPM }
| "==" { EQ }
| "&&" { AND }
| "||" { OR }
| "=>" { IMP }
| id as x         { ID x }
| _  as c { raise (ParseError (Printf.sprintf "At offset %d: unexpected character %c.\n" (Lexing.lexeme_start lexbuf) c)) }
| eof { EOF }