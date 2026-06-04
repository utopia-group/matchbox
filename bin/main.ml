open Core
open Matchbox

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

let incr =
  let open Command.Let_syntax in
  Command.basic
    ~summary:"Apply a stream of rule updates incrementally, computing only per-table deltas"
  [%map_open
    let path = anon ("program" %: string)
    and config = flag "--config" (optional string) ~doc:"JSON file of initial runtime rules"
    and updates = flag "--updates" (required string)
      ~doc:"JSON file of updates; each element is an op object ({\"op\": \"insert\"|\"delete\", ...rule fields}) or a list of ops forming one atomic batch"
    and check = flag "--check" no_arg ~doc:"After each batch, compare every table against a full recomputation"
    and time = flag "--time" no_arg ~doc:"Print per-batch timing (with --check, also full-recompute timing)"
    and strict = flag "--strict" no_arg ~doc:"Error (instead of warn-and-skip) when a delete matches no row"
    and verbose = flag "--verbose" no_arg ~doc:"Also list unchanged tables"
    in fun () ->
      let parsed = Parse.parse_program path |> Result.ok_or_failwith in
      let ctx = ParserContext.typecheck parsed in
      let rows =
        match config with
        | None -> []
        | Some file -> RuntimeInterface.parse_raw_rows ctx.typs file
      in
      let derived = Incremental.derived_names ctx.prog in
      let batches = Incremental.parse_updates_file ctx.typs ~derived updates in
      let nonce = Incremental.has_nonce ctx.prog in
      if check && nonce then
        eprintf
          "warning: program uses nonce; --check is skipped (incremental \
           execution continues nonce counters, a full recompute renumbers \
           them from zero)\n%!";
      let st = Incremental.bootstrap ctx.prog rows in
      Printf.printf "bootstrap: %d base rows, %d steps, %d batches\n%!"
        (List.length rows) (List.length ctx.prog) (List.length batches);
      let any_failed = ref false in
      let total_incr = ref 0. in
      let (_ : Incremental.state) =
        List.foldi batches ~init:st ~f:(fun i st batch ->
          List.iter batch ~f:(fun op ->
            Printf.printf "== update %d: %s\n" (i + 1) (Incremental.op_to_string op));
          let c = Clock.start () in
          let st, deltas = Incremental.apply_batch ~strict st ctx.prog batch in
          let elapsed = Clock.stop c in
          total_incr := !total_incr +. elapsed;
          List.iter deltas ~f:(fun (name, delta) ->
            if not (Incremental.Delta.is_empty delta) then begin
              Printf.printf "Δ %s: +%d -%d\n%s\n" name
                (List.length delta.ins) (List.length delta.del)
                (Incremental.Delta.to_string delta)
            end
            else if verbose then Printf.printf "Δ %s: no change\n" name);
          if time then Printf.printf "[time] incremental: %.3fms\n" elapsed;
          if check && not nonce then begin
            let c = Clock.start () in
            let results = Incremental.verify_against_full st ctx.prog in
            let full_time = Clock.stop c in
            let bad = List.filter results ~f:(fun (_, ok) -> not ok) in
            if List.is_empty bad then
              Printf.printf "[check] PASS (%d tables match full recompute%s)\n"
                (List.length results)
                (if time then sprintf "; full recompute: %.3fms" full_time else "")
            else begin
              any_failed := true;
              List.iter bad ~f:(fun (name, _) ->
                Printf.printf "[check] FAIL: %s differs from full recompute\n" name)
            end
          end;
          Printf.printf "%!";
          st)
      in
      if time then
        Printf.printf "[time] total incremental: %.3fms over %d batches\n%!"
          !total_incr (List.length batches);
      if !any_failed then exit 1
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
  "incr", incr;
  "strike", main;
  "verify", verify
]