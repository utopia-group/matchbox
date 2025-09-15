open Core
open BaseLogic
open Semantics

let unvar = Map.fold ~init:String.Map.empty ~f:(fun ~key ~data ->
  Map.add_exn ~key:(Var.str key) ~data
)

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


let rec eval_match_expr (matches : MatchExpression.t) (expr : Gpl.Expr.t) : Match.t =
  match expr with 
  | BV (value, width) -> Bit.Vector.of_int (Bigint.to_int_exn value) ~width |> Match.Exact
  | Var x -> (
    match MatchExpression.findv matches x with
    | Some match_val -> match_val
    | None -> failwith (sprintf "Variable not found in matches: %s" (Var.str x)))
  | BinOp (op, e1, e2) ->
    let tv1 = eval_match_expr matches e1 in 
    let tv2 = eval_match_expr matches e2 in 
    tv_eval2 op tv1 tv2
  | UnOp (op, e) ->
    eval_match_expr matches e 
    |> tv_eval1 op
  | Apply _ -> failwith "apply??????"

  let apply_in_tfx (row : MatchAction.t) tfx : MatchActionTable.t =
    let open MatchActionTable.MonadicSyntax in 
    let open MatchTfx in
    match tfx with
    | Del x -> 
      return (MatchAction.remove_keyv row x)
    | WildCard x ->
      let wild = Match.Ternary(Trit.Vector.wc (Var.width x)) in
      return (MatchAction.set_matchv row x wild)
    | Project vars ->
      (* Keep only the specified variables *)
      return (MatchAction.match_projectv row vars)
    | SetTo (x, expr) ->
      (* Set a variable to the result of evaluating an expression *)
      let new_match = eval_match_expr row.matches expr in
      return (MatchAction.set_matchv row x new_match)
    | CubeFilter cube -> 
      MatchAction.refine row cube
      |> Option.value_map ~f:return ~default:empty
    | Filter phi -> 
      Cover.split `TCAM row.matches phi
      |> MatchAction.update_with_matches_list row

let eval_action_expr data expr =
  let open Gpl.Expr in 
  let model = Data.to_gpl_model data in 
  let v, w = eval model expr |> Result.ok_or_failwith in
  Bit.Vector.of_int (Bigint.to_int_exn v) ~width:w

let apply_out_tfx row tfx =
  let action = MatchAction.get_action row in 
  let data = MatchAction.get_data row in 
  let action, data =
    let open OutTfx in 
    match tfx with
    | Project vars ->
      (* Keep only the specified action parameters *)
      action, 
      Data.projectv data vars
    | SetTo (x, expr) ->
      (* Set a parameter to the result of evaluating an expression *)
      let value = eval_action_expr data expr in
      action, 
      Data.updatev data x value
    | Del x -> 
      action, 
      Data.removev data x
    | Rename (old_action,new_action) when MagmaAction.equal old_action action -> 
      new_action,
      data
    | Rename _ -> 
      action,
      data
    in
    {row with action; data}

let rec eval (clause : Clause.t) (config : Config.t) : MatchActionTable.t =
  let open MatchActionTable.MonadicSyntax in 
  match clause with
  | Id (f,_) -> get_mat config f
  | Table (t, _) -> t
  | Join (f, g, _) ->
    let* f_row = eval f config in
    let* g_row = eval g config in
    MatchAction.pair f_row g_row
    |> Option.value_map ~default:empty ~f:return
  | Compose (f, g, _) ->
    let g_mat = eval g config in 
    let+ f_row = eval f config in
    let (action, data) = MatchActionTable.run g_mat f_row.data in 
    MatchAction.{f_row with action;data}
  | MapOut (f, tfx, _) ->
    let+ row = eval f config in
    apply_out_tfx row tfx 
  | MapIn (f, tfx, _) ->
    let* row = eval f config in
    apply_in_tfx row tfx

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
