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

let verify =
  let open Command.Let_syntax in
  Command.basic ~summary:"Verify Hoare properties (assert ... => ...) in a program via Z3"
  [%map_open
    let path = anon ("program" %: string)
    and input_file = flag "--config" (optional string) ~doc:"JSON file of runtime rules (needed for tables whose rows come from a config)"
    in fun () ->
      let parsed = Parse.parse_program path |> Result.ok_or_failwith in
      let ctx = ParserContext.typecheck parsed in
      let init_config =
        match input_file with
        | None -> BaseLogic.Config.empty
        | Some rules -> RuntimeInterface.parse_trace_file ctx.typs rules
      in
      let results, _ = BaseInterpreter.eval_program init_config ctx.prog in
      if List.is_empty ctx.props then
        Printf.printf "No properties (assert <table> : { .. } => { .. }) found in %s\n%!" path
      else begin
        let any_failed = ref false in
        List.iter ctx.props ~f:(fun (p : Property.t) ->
          match List.Assoc.find results p.table ~equal:String.equal with
          | None ->
            any_failed := true;
            Printf.printf "?? %s: table not produced by the program\n%!" p.table
          | Some tbl ->
            let typ = Type.find_table_exn ctx.typs p.table in
            match Verifier.check typ tbl p with
            | Verifier.Valid ->
              Printf.printf "VALID:    %s |= %s\n%!" p.table (Property.to_string p)
            | Verifier.Counterexample binds ->
              any_failed := true;
              let pkt =
                List.map binds ~f:(fun (k, v) -> Printf.sprintf "%s=%s" k v)
                |> String.concat ~sep:", "
              in
              Printf.printf "VIOLATED: %s |/= %s\n          counterexample: %s\n%!"
                p.table (Property.to_string p) pkt)
        ;
        if !any_failed then exit 1
      end
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
  "strike", main;
  "verify", verify
]