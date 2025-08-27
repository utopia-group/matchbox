open Core
open BaseLogic
open Semantics

let get_mat (config : Config.t) (symbol : Symbol.t) : MatchActionTable.t =
  try
    let provtable = Config.find_exn config symbol in
    List.map provtable.rows ~f:(fun provrow -> provrow.row)
  with _ -> []

let rec eval (expr : TransformExpr.t) (config : Config.t) : MatchActionTable.t =
  match expr with
  | TableLiteral mat -> mat
  | TableSymbol symbol -> (
    match List.find config.symbols ~f:(Symbol.( = ) symbol) with
    | Some symbol -> get_mat config symbol
    | None -> [])
  | Compose (c1, c2) ->
    let mat1 = eval c1 config in
    let mat2 = eval c2 config in
    List.fold mat1 ~init:[] ~f:(fun acc row1 ->
        let action1 = MatchAction.get_action row1 in
        let output_keys = Action.get_data action1 in
        List.fold mat2 ~init:acc ~f:(fun acc row2 ->
            if MatchAction.does_match output_keys row2 then
              let matches1 = MatchAction.get_matches row1 in
              let action2 = MatchAction.get_action row2 in
              let composed_row = MatchAction.make matches1 action2 in
              composed_row :: acc
            else acc))
    |> List.rev
  | Join (c1, c2, alignment) ->
    let mat1 = eval c1 config in
    let mat2 = eval c2 config in
    List.fold mat1 ~init:[] ~f:(fun acc row1 ->
        List.fold mat2 ~init:acc ~f:(fun acc row2 ->
            match
              MatchAction.pair row1 row2 ~f:(JoinExp.eval_exn alignment)
            with
            | None -> acc
            | Some joined_row -> joined_row :: acc))
    |> List.rev
  | Project (c, fields) ->
    let mat = eval c config in
    List.map mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let filtered_matches =
          Map.filter_keys matches ~f:(List.mem fields ~equal:String.equal)
        in
        let action_data = Action.get_data action in
        let filtered_action_data =
          Map.filter_keys action_data ~f:(List.mem fields ~equal:String.equal)
        in
        let filtered_action =
          Action.make (Action.get_name action) filtered_action_data
        in
        MatchAction.make filtered_matches filtered_action)
  | Filter (c, filter_matches) ->
    let mat = eval c config in
    List.filter_map mat ~f:(fun row ->
        let row_matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let action_data = Action.get_data action in
        let all_filter_fields_present =
          Map.for_alli filter_matches ~f:(fun ~key ~data:_ ->
              Map.mem row_matches key)
        in
        if not all_filter_fields_present then None
        else
          (* Compute ρ.μ /\ μ *)
          let intersection_matches =
            Map.fold row_matches ~init:(Some row_matches)
              ~f:(fun ~key ~data:row_match acc ->
                match acc with
                | None -> None
                | Some result_map -> (
                  match Map.find filter_matches key with
                  | None -> Some result_map
                  | Some filter_match -> (
                    match Match.intersect row_match filter_match with
                    | None -> None
                    | Some intersected_match ->
                      Some (Map.set result_map ~key ~data:intersected_match))))
          in
          match intersection_matches with
          | None ->
            (* ρ.μ /\ μ = empty, so filter out this row *)
            None
          | Some intersected_matches ->
            (* Check if ρ.ν ∈ μ *)
            let action_contained_in_filter =
              Map.for_alli action_data
                ~f:(fun ~key:field_name ~data:field_value ->
                  match Map.find filter_matches field_name with
                  | None ->
                    (* Field not constrained by filter *)
                    true
                  | Some filter_match -> Match.matches field_value filter_match)
            in
            if action_contained_in_filter then
              Some (MatchAction.make intersected_matches action)
            else None)
  | RenameKeys (c, renaming) ->
    let mat = eval c config in
    List.map mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let renamed_matches = apply_field_renaming matches renaming in
        MatchAction.make renamed_matches action)
  | RenameActions (c, renaming) ->
    let mat = eval c config in
    List.map mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let action_name = Action.get_name action in
        let renamed_action_name = apply_action_renaming action_name renaming in
        let renamed_action = Action.set_name renamed_action_name action in
        MatchAction.make matches renamed_action)
  | Invert c ->
    let mat = eval c config in
    List.bind mat ~f:(fun row ->
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
  | WriteData (c, assignments) ->
    let mat = eval c config in
    List.map mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let updated_action =
          apply_assignments_to_action action assignments config
        in
        MatchAction.make matches updated_action)
  | WriteKey (c, assignments) ->
    let mat = eval c config in
    List.map mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let extended_matches =
          apply_assignments_to_matches matches assignments config
        in
        MatchAction.make extended_matches action)

and apply_field_renaming matches renaming =
  List.fold renaming ~init:matches ~f:(fun acc (old_name, new_name) ->
      match Map.find acc old_name with
      | Some value ->
        Map.remove acc old_name |> Map.set ~key:new_name ~data:value
      | None -> acc)

and apply_action_renaming action_name renaming =
  List.fold renaming ~init:action_name ~f:(fun acc (old_name, new_name) ->
      if String.(acc = old_name) then new_name else acc)

and apply_assignments_to_action action assignments _config =
  List.fold assignments ~init:action ~f:(fun acc (field, value) ->
      Action.update_data acc field value)

and apply_assignments_to_matches matches assignments _config =
  List.fold assignments ~init:matches ~f:(fun acc (field, value) ->
      Map.set acc ~key:field ~data:(Match.exact value))
