open Core
open BaseLogic
open Semantics

let get_mat (config : Config.t) (symbol : Symbol.t) : MatchActionTable.t =
  try
    let provtable = Config.find_exn config symbol in
    List.map provtable.rows ~f:(fun provrow -> provrow.row)
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

let eval (clause : Clause.t) (config : Config.t) : MatchActionTable.t =
  match clause with
  | Id f -> get_mat config f
  | Join (f, g, merge) ->
    let f_mat = get_mat config f in
    let g_mat = get_mat config g in
    List.fold f_mat ~init:[] ~f:(fun acc f_row ->
        List.fold g_mat ~init:acc ~f:(fun acc g_row ->
            match MatchAction.pair f_row g_row ~f:(JoinExp.eval_exn merge) with
            | None -> acc
            | Some joined_row -> joined_row :: acc))
    |> List.rev
  | Compose (f, g) ->
    let f_mat = get_mat config f in
    let g_mat = get_mat config g in
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
  | Invert f ->
    (* Swap matches and actions *)
    let f_mat = get_mat config f in
    List.bind f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let action_name = Action.get_name action in
        let action_data = Action.get_data action in
        let new_matches = Map.map action_data ~f:Match.exact in
        let new_action_args = Map.map matches ~f:Match.unsafe_explicit_set in
        (* Handle multiple possible action arg combinations *)
        let args_combinations = ProvRow.pivot new_action_args in
        List.map args_combinations ~f:(fun args ->
            let new_action = Action.make action_name args in
            MatchAction.make new_matches new_action))
  | MapOut (f, tfx) ->
    let f_mat = get_mat config f in
    List.map f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let transformed_action = apply_action_tfx action tfx in
        MatchAction.make matches transformed_action)
  | MapIn (f, tfx) ->
    let f_mat = get_mat config f in
    List.map f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let transformed_matches = apply_match_tfx matches tfx in
        MatchAction.make transformed_matches action)
