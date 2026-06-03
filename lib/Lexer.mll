{
  open Core
  open Parser

  exception ParseError of string

}

let id = ['a'-'z' 'A'-'Z' '_'] (['.']? ['a'-'z' 'A'-'Z' '0'-'9' '_'])* 
let bp = "0b" ['0' '1' '*']+

rule tokens = parse
| "//" [^ '\n']* { tokens lexbuf }
| [' ' '\t' '\n'] { tokens lexbuf }
| ['0'-'9']+ as i { INT (Int.of_string i) }
| "action" { ACTION }
| "else" { ELSE }
| "key" { KEY }
| "data" { DATA }
| "to" { TO }
(* | "limit" { LIMIT } *)
| "rows" { ROWS }
| "assume" { ASSUME }
| "assert" { ASSERT }
| "$action" { ACTIONVAR }
| "forall" { FORALL }
| "private" { PRIVATE }
| "o--" { MATCHSTICK }
| "->" { ARROW }
| "--->" { FDARROW }
| ">>" { COMPOSE }
| "|>" { OVERRIDE }
| ":=" { ASSIGN }
| ";" { SEMICOLON }
| ":" { COLON }
| "," { COMMA }
| "*" { TIMES }
| "." { DOT }
| "|" { BAR }
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
| "cube_filter" { CUBE_FILTER }
| "filter" { FILTER }
| "rename" { RENAME }
| "tcam" { TCAM }
| "cam" { CAM }
| "lpm" { LPM }
| "==" { EQ }
| "&&" { AND }
| "&" { BAND }
| "||" { OR }
| "=>" { IMP }
| id as x         { ID x }
| bp as x         { BP x }
| _  as c { raise (ParseError (Printf.sprintf "At offset %d: unexpected character %c.\n" (Lexing.lexeme_start lexbuf) c)) }
| eof { EOF }