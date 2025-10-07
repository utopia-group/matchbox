open Core
open Stijl

module Parser = struct
  

(* Prints the line number and character number where the error occurred.*)
let print_error_position (lexbuf : Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  Fmt.str "Line:%d Position:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_program filepath =
  Printf.printf "reading %s\n%!" filepath;
  let channel = In_channel.create filepath in
  Printf.printf "success!... Lexing\n%!";
  let lexbuf = Lexing.from_channel channel in
  Printf.printf "Success!.... closing\n%!";
  Printf.printf "Closed!... parsing\n%!";
  let program = 
    try Ok (Parser.matchstix Lexer.tokens lexbuf) with
    (* catch exception and turn into Error *)
    (* | SyntaxError msg ->
      let error_msg = Fmt.str "%s: %s@." (print_error_position lexbuf) msg in
      Error (Error.of_string error_msg) *)
      | Parser.Error ->
        let error_msg = Fmt.str "%s: syntax error@." (print_error_position lexbuf) in
        failwith error_msg
  in
  In_channel.close channel;
  program
end


let main = 
  let open Command.Let_syntax in 
  Command.basic ~summary:"Typecheck a matchstix program"
  [%map_open
    let path = anon ("program" %: string) in
    fun () ->
      try 
        Parser.parse_program path
        |> Result.ok_or_failwith
        |> ParserContext.typecheck
      with
      | Failure msg -> 
        Printf.printf "%s\n" msg;
        exit 1
  ]

let () = Command_unix.run main
