open Core

(* Prints the line number and character number where the error occurred.*)
let print_error_position (lexbuf : Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Fmt.str "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_program filepath =
  let channel = In_channel.create filepath in
  let lexbuf = Lexing.from_channel channel in
  let program =
    try Ok (Parser.matchstix Lexer.tokens lexbuf) with
    | Parser.Error ->
      let error_msg = Fmt.str "%s: syntax error@." (print_error_position lexbuf) in
      failwith error_msg
  in
  In_channel.close channel;
  program

let parse_string source =
  let lexbuf = Lexing.from_string source in
  try Ok (Parser.matchstix Lexer.tokens lexbuf) with
  | Parser.Error ->
    let error_msg = Fmt.str "%s: syntax error@." (print_error_position lexbuf) in
    failwith error_msg
