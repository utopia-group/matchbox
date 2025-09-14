open Core
open BaseLogic
open Semantics

let get_mat (config : Config.t) (symbol : Symbol.t) : MatchActionTable.t =
  try Config.find_exn config symbol with _ -> []

let tv_eval2 op tv1 tv2 : Match.t =
  let open Gpl.Expr in
  match op with 
  | BAnd -> Match.(tv1 && tv2)
  | BOr -> Match.(tv1 || tv2)
  | _ -> failwith "to implement"

let tv_eval1 op (m : Match.t) : Match.t = 
  let open Gpl.Expr in
  match op with 
  | UNeg -> Match.not m
  | _ -> failwith "arith negative?"


let rec eval_match_expr (matches : Match.t Var.Map.t) (expr : Gpl.Expr.t) : Match.t =
  match expr with
  | BV (value, width) -> Bit.Vector.of_int (Bigint.to_int_exn value) ~width |> Match.Exact
  | Var var_name -> (
    match Map.find matches var_name with
    | Some match_val -> match_val
    | None -> failwith (sprintf "Variable not found in matches: %s" (Var.str var_name)))
  | BinOp (op, e1, e2) ->
    let tv1 = eval_match_expr matches e1 in 
    let tv2 = eval_match_expr matches e2 in 
    tv_eval2 op tv1 tv2
  | UnOp (op, e) ->
    eval_match_expr matches e 
    |> tv_eval1 op
  | Apply _ -> failwith "apply??????"


  let apply_match_tfx matches tfx =
    let open MatchTfx in
    match tfx with
    | Del x -> 
      Map.remove matches x
    | Project vars ->
      (* Keep only the specified variables *)
      Map.filter_keys matches ~f:(List.mem vars ~equal:Var.equal)
    | SetTo (var, expr) ->
      (* Set a variable to the result of evaluating an expression *)
      let new_match = eval_match_expr matches expr in
      Map.set matches ~key:var ~data:new_match
    | Filter _ -> failwith "todo"
    | CubeFilter cube -> 
      Map.filter_mapi matches ~f:(fun ~key ~data ->
        match Map.find cube (Var.str key) with 
        | None -> Some data 
        | Some mexpr -> 
          Match.intersect mexpr data
      )
      

let rec apply_action_tfx action tfx =
  let open ActionTfx in 
  match tfx with
  | Project vars ->
    (* Keep only the specified action parameters *)
    Action.project_data (List.map ~f:Var.str vars) action
  | SetTo (var, expr) ->
    (* Set a parameter to the result of evaluating an expression *)
    let new_data = eval_action_expr action expr in
    Action.update_data action (Var.str var) new_data
  | Del x -> 
    let ys = Action.get_data action |> Map.key_set in 
    let ys' = Set.remove ys (Var.str x) in 
    Action.project_data (Set.to_list ys') action
  | Rename (a1, a2) when String.(a1 = Action.get_name action) -> 
    Action.make a2 (Action.get_data action)
  | Rename _ -> 
    action

and eval_action_expr action expr =
  let open Gpl.Expr in 
  let model = Action.get_data action in
  let model = Map.fold model ~init:Var.Map.empty ~f:(fun ~key ~data acc ->
    Map.set ~key:(Var.make key (Bit.Vector.length data)) ~data acc 
  ) in 
  let model = Var.Map.map model ~f:(fun bv -> Bigint.of_int (Bit.Vector.to_int bv), Bit.Vector.length bv) in
  let v, w = eval model expr |> Result.ok_or_failwith in
  Bit.Vector.of_int (Bigint.to_int_exn v) ~width:w


let apply_action_tfx action tfx =
  match tfx with
  | ActionTfx.Project vars ->
    (* Keep only the specified action parameters *)
    Action.project_data vars action
  | SetTo (var, expr) ->
    (* Set a parameter to the result of evaluating an expression *)
    let new_data = eval_action_expr action expr in
    Action.update_data action var new_data
  | Filter _ -> failwith "todo"

let rec eval (clause : Clause.t) (config : Config.t) : MatchActionTable.t =
  match clause with
  | Id (f,_) -> get_mat config f
  | Join (f, g, _) ->
    let f_mat = eval f config in
    let g_mat = eval g config in
    List.fold f_mat ~init:[] ~f:(fun acc f_row ->
        List.fold g_mat ~init:acc ~f:(fun acc g_row ->
            match MatchAction.pair f_row g_row ~f:(fun _ -> failwith "joiN?") with
            | None -> acc
            | Some joined_row -> joined_row :: acc))
    |> List.rev
  | Compose (f, g, _) ->
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
  | MapOut (f, tfx, _) ->
    let f_mat = eval f config in
    List.map f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let action = MatchAction.get_action row in
        let transformed_action = apply_action_tfx action tfx in
        MatchAction.make matches transformed_action)
  | MapIn (f, tfx, _) ->
    let f_mat = eval f config in
    List.map f_mat ~f:(fun row ->
        let matches = MatchAction.get_matches row in
        let matches = Map.fold matches ~init:Var.Map.empty ~f:(fun ~key ~data acc -> 
          Map.set acc ~key:(Var.make key (Match.length data)) ~data
        ) in
        let action = MatchAction.get_action row in
        let transformed_matches = apply_match_tfx matches tfx in
        let transformed_matches = Map.fold transformed_matches ~init:String.Map.empty ~f:(fun ~key ~data:_ acc -> 
          Map.set acc ~key:(Var.str key) ~data:(failwith "")
        ) in
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
            Map.set current_config.cfg ~key:step.defined.name ~data:result_table;
        }
    in
    (new_config, (step.defined.name, result_table) :: accumulated_results)
  in
  let final_config, step_results =
    List.fold program ~init:(initial_config, []) ~f:execute_step
  in
  (List.rev step_results, final_config)
