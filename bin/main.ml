open Core
open Stijl

let main = 
  let open Command.Let_syntax in 
  Command.basic ~summary:"Typecheck (and run) a matchstix program"
  [%map_open
    let path = anon ("program" %: string) 
    and input_file = flag "--config" (optional string) ~doc:"File containing input configuration rules in JSON format"
    in fun () ->
      let parsed = Parse.parse_program path |> Result.ok_or_failwith in
      let ctx = ParserContext.typecheck parsed in
      match input_file with 
      | None -> ()
      | Some rules ->
        let config = RuntimeInterface.parse_trace_file ctx.typs rules in 
        Printf.printf "START:\n%s*********************************\n" (BaseLogic.Config.to_string config);
        BaseInterpreter.eval_program config ctx.prog
        |> snd
        |> BaseLogic.Config.to_string
        |> Printf.printf "%s%!"      
  ]

let exp =
  let open Command.Let_syntax in 
  Command.basic ~summary:"Run experiments based a driver file"
  [%map_open
    let path = anon ("driver" %: string)
    and minimize = flag "--minimize" no_arg ~doc:"Check table size optimizality"
    in fun () ->
      ExpDriver.run path minimize
  ]

let () = Command_unix.run @@ Command.group 
~summary:"matchbox toolkit"
[
  "exp", exp;
  "strike", main
]