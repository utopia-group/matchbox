open Core
open Yojson
type t = {
  name : string; 
  progpath: string; 
  config : string
} [@@deriving yojson]


let parse_program path = 
  Parse.parse_program path 
  |> Result.ok_or_failwith

let run_program config (ctx : ParserContext.t) =
  let c = Clock.start () in
  let config' = BaseInterpreter.eval config ctx.prog in
  let eval_time = Clock.stop c in  
  let eval_in_size = BaseLogic.Config.size config in
  let eval_out_size = BaseLogic.Config.size config' in
  let c = Clock.start() in
  let min_eval_size = GuardSynthesis.minimize config' in
  let min_eval_time = Clock.stop c +. eval_time in
  let stats = {ctx.stats with 
    eval_time; eval_in_size; eval_out_size;
    min_eval_time; min_eval_size;
  } in
  ParserContext.{ctx with stats}
let run_ : Safe.t -> unit = function
  | `List ls -> 
    Stats.print_header ();
    List.iter ls ~f:(fun json ->
      let {name;progpath;config} = of_yojson json |> Result.ok_or_failwith in 
      let prog = parse_program progpath in 
      let pctx = ParserContext.typecheck prog in 
      let inconfig = RuntimeInterface.parse_trace_file pctx.typs config in 
      let pctx = run_program inconfig pctx in
      Stats.println name pctx.stats
    )
  | json -> 
    failwithf "unrecognized experiment format %s" (Safe.to_string json) ()


let run filepath = 
  run_ (Safe.from_file filepath)
  
