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
    | Parser.Error ->
      let error_msg = Fmt.str "%s: syntax error@." (print_error_position lexbuf) in
      failwith error_msg
  in
  In_channel.close channel;
  program
end


let main = 
  let open Command.Let_syntax in 
  Command.basic ~summary:"Typecheck (and run) a matchstix program"
  [%map_open
    let path = anon ("program" %: string) 
    and input_file = flag "--config" (optional string) ~doc:"E configuration rules"
    in fun () ->
      let ctx = 
        Parser.parse_program path
        |> Result.ok_or_failwith
        |> ParserContext.typecheck
      in
      match input_file with 
      | None -> ()
      | Some rules ->
        let config = RuntimeInterface.parse_trace_file ctx.typs rules in 
        BaseInterpreter.eval_program config ctx.prog
        |> snd
        |> BaseLogic.Config.to_string
        |> Printf.printf "%s%!"
      
  ]

let () = Command_unix.run main
