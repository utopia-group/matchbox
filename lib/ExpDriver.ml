open Core
open Yojson

type t = {
  name : string; 
  progpath: string; 
  input : string;
  output : string option;
} [@@deriving yojson]

let parse_program path = 
  path
  |> Parse.parse_program
  |> Result.ok_or_failwith

let run_program config (ctx : ParserContext.t) (minimize : bool)
  : BaseLogic.Config.t * ParserContext.t =
  let c = Clock.start () in
  let config' = BaseInterpreter.eval config ctx.prog in
  let eval_time = Clock.stop c in  
  let eval_in_size = BaseLogic.Config.size config in
  let eval_out_size = BaseLogic.Config.size config' in
  let min_eval_size, min_eval_time =
    if minimize then
      let c = Clock.start() in
      GuardSynthesis.minimize config', Clock.stop c +. eval_time
    else (0, 0.)
  in
  let stats = {ctx.stats with 
    eval_time; eval_in_size; eval_out_size;
    min_eval_time; min_eval_size;
  } in
  config', ParserContext.{ctx with stats}

let run_ (json : Safe.t) (minimize : bool) : unit =
  match json with
  | `List ls -> 
    Stats.print_header ();
    List.iter ls ~f:(fun json ->
      let {name;progpath;input;output} = of_yojson json |> Result.ok_or_failwith in
      let pctx = parse_program progpath in 
      let pctx = ParserContext.typecheck pctx in 
      let config = RuntimeInterface.parse_trace_file pctx.typs input in 
      let config', pctx = run_program config pctx minimize in
      (* Do not output ghost tables *)
      let config' = BaseLogic.Config.{
        symbols = Set.filter config'.symbols 
          ~f:(fun s -> not (Map.find_exn pctx.typs s).is_ghost);
        cfg = Map.filter_keys config'.cfg
          ~f:(fun key -> not (Map.find_exn pctx.typs key).is_ghost)
        }
      in
      Option.iter output ~f:(fun output ->
        Safe.to_file output (RuntimeInterface.config_to_json config')
      );
      Stats.println name pctx.stats
    )
  | json -> 
    failwithf "unrecognized experiment format %s" (Safe.to_string json) ()


let run (filepath : string) (minimize : bool) : unit = 
  run_ (Safe.from_file filepath) minimize
