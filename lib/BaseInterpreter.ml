open Core
open BaseLogic
open Semantics

let get_mat (config : Config.t) (symbol : Symbol.t) : MatchActionTable.t =
  try
    Config.find_exn config symbol 
  with _ -> []

let rec apply_match_tfx matches tfx =
  match tfx with
  | MatchTfx.Project vars ->
    (* Keep only the specified variables *)
    Map.filter_keys matches ~f:(List.mem vars ~equal:String.equal)
  | SetTo (var, expr) ->
    (* Set a variable to the result of evaluating an expression *)
    let new_match = eval_match_expr matches expr in
    Map.set matches ~key:var ~data:new_match
  | Filter _ -> failwith "todo"

and eval_match_expr matches expr =
  match expr with
  | Var var_name -> (
    match Map.find matches var_name with
    | Some match_val -> match_val
    | None -> failwith (sprintf "Variable not found in matches: %s" var_name))
  | Match match_val -> match_val
  | AddK (inner_expr, bv) -> (
    let base_match = eval_match_expr matches inner_expr in
    match base_match with
    | Match.Exact base_bv ->
      let result_bv = Bit.Vector.(base_bv + bv) in
      Match.Exact result_bv
    | _ -> failwith "AddK operation requires exact match")
  | SubK (inner_expr, bv) -> (
    let base_match = eval_match_expr matches inner_expr in
    match base_match with
    | Match.Exact base_bv ->
      (* Subtraction via two's complement: a - b = a + (~b + 1) *)
      let neg_bv = Bit.Vector.(incr (not bv)) in
      let result_bv = Bit.Vector.(base_bv + neg_bv) in
      Match.Exact result_bv
    | _ -> failwith "SubK operation requires exact match")

let rec apply_action_tfx action tfx =
  match tfx with
  | ActionTfx.Project vars ->
    (* Keep only the specified action parameters *)
    Action.project_data vars action
  | SetTo (var, expr) ->
    (* Set a parameter to the result of evaluating an expression *)
    let new_data = eval_action_expr action expr in
    Action.update_data action var new_data
  | Filter _ -> failwith "todo"

and eval_action_expr action expr =
  match expr with
  | Var var_name -> (
    match Action.get_datum action var_name with
    | Some data_val -> data_val
    | None -> failwith (sprintf "Variable not found in action: %s" var_name))
  | Data data_val -> data_val
  | AddK (inner_expr, bv) ->
    let base_data = eval_action_expr action inner_expr in
    Bit.Vector.(base_data + bv)
  | SubK (inner_expr, bv) ->
    let base_data = eval_action_expr action inner_expr in
    let neg_bv = Bit.Vector.(incr (not bv)) in
    Bit.Vector.(base_data + neg_bv)

let rec eval (clause : Clause.t) (config : Config.t) : MatchActionTable.t =
  match clause with
  | Id f -> get_mat config f
  | Join (f, g, merge) ->
    let f_mat = eval f config in
    let g_mat = eval g config in
    List.fold f_mat ~init:[] ~f:(fun acc f_row ->
        List.fold g_mat ~init:acc ~f:(fun acc g_row ->
            match MatchAction.pair f_row g_row ~f:(JoinExp.eval_exn merge) with
            | None -> acc
            | Some joined_row -> joined_row :: acc))
    |> List.rev
  | Compose (f, g) ->
    let f_mat = eval f config in
    let g_mat = eval g config in
    List.fold f_mat ~init:[] ~f:(fun acc f_row ->
        let f_action = MatchAction.get_action f_row in
        let output_keys = Action.get_data f_action in
        List.fold g_mat ~init:acc ~f:(fun acc g_row ->
            if MatchAction.does_match output_keys g_row then
              let f_matches = MatchAction.get_matches f_row in
              let g_action = MatchAction.get_action g_row in
              let composed_row = MatchAction.make f_matches g_action in
              composed_row :: acc
            else acc))
    |> List.rev
  | MapOut (f, tfx) ->
    let f_mat = eval f config in
    List.map f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let transformed_action = apply_action_tfx action tfx in
        MatchAction.make matches transformed_action)
  | MapIn (f, tfx) ->
    let f_mat = eval f config in
    List.map f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let transformed_matches = apply_match_tfx matches tfx in
        MatchAction.make transformed_matches action)

(* Execute a list of BaseLogic Clauses step by step *)
let eval_program (initial_config : Config.t) (program : BaseLogic.t list) :
    (string * MatchActionTable.t) list * Config.t =
  let execute_step (current_config, accumulated_results) step =
    let result_table = eval step.definition current_config in
    let new_config =
      BaseLogic.Config.
        {
          symbols = step.defined :: current_config.symbols;
          cfg =
            Map.set current_config.cfg ~key:step.defined.name
              ~data:result_table
        }
    in
    (new_config, (step.defined.name, result_table) :: accumulated_results)
  in
  let final_config, step_results =
    List.fold program ~init:(initial_config, []) ~f:execute_step
  in
  (List.rev step_results, final_config)
