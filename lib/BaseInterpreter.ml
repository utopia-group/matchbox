open Core
open BaseLogic
open Semantics

module Noncer = struct 
  type t = { 
    next : Bit.Vector.t;
  }

  let empty width = {next = Bit.Vector.zero width}

  let next noncer = 
      let nonce = noncer.next in 
      let next = Bit.Vector.incr noncer.next in
      let noncer = {next} in 
      noncer, nonce
end

module NonceState = struct 
  type t = Noncer.t Var.Map.t

  let empty = Var.Map.empty

  let set_noncer (state : t) (x : Var.t) noncer : t =
    Map.set state ~key:x ~data:noncer 


  let find_noncer (state : t) (x : Var.t) = 
    match Map.find state x  with 
    | Some noncer -> state, noncer
    | None -> 
      let noncer = Noncer.empty (Var.width x) in
      let state = Map.set state ~key:x ~data:noncer in 
      state, noncer

  let get state x : t * Bit.Vector.t = 
    let state, noncer = find_noncer state x in
    let noncer = noncer.next in
    state, noncer
    
end

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
    let hw = MatchAction.exfil_hardware row in 
    GuardSynthesis.split hw row.matches phi
    |> MatchAction.update_with_matches_list row

let eval_action_expr data expr =
  let open Gpl.Expr in 
  let model = Data.to_gpl_model data in 
  let v, w = eval model expr |> Result.ok_or_failwith in
  Bit.Vector.of_int (Bigint.to_int_exn v) ~width:w

let apply_out_tfx state row tfx =
  let action = MatchAction.get_action row in 
  let data = MatchAction.get_data row in 
  let state, action, data =
    let open OutTfx in 
    match tfx with
    | Nonce x -> 
      let state, v = NonceState.get state x in
      state, action, Data.updatev data x v
    | Project vars ->
      (* Keep only the specified action parameters *)
      state, 
      action, 
      Data.projectv data vars
    | SetTo (x, expr) ->
      (* Set a parameter to the result of evaluating an expression *)
      let value = eval_action_expr data expr in
      state,
      action, 
      Data.updatev data x value
    | Del x -> 
      state,
      action, 
      Data.removev data x
    | Rename (old_action,new_action) when MagmaAction.equal old_action action -> 
      state,
      new_action,
      data
    | Rename _ -> 
      state,
      action,
      data
    in
    state, {row with action; data}

let rec eval_inner (clause : Clause.t) (config : Config.t) (state : NonceState.t) : NonceState.t * MatchActionTable.t =
  let open MatchActionTable.MonadicSyntax in 
  match clause with
  | Id (f,_) -> 
    state, get_mat config f
  | Table (_, t, _) -> 
    state, t
  | Join (f, g, _) ->
    let state, f_mat = eval_inner f config state in
    let state, g_mat = eval_inner g config state in
    state, 
    let* f_row = f_mat in 
    let* g_row = g_mat in
    MatchAction.pair f_row g_row
    |> Option.value_map ~default:empty ~f:return
  | Override (f, g, _) ->
    let state, f_mat = eval_inner f config state in
    let state, g_mat = eval_inner g config state in
    state, f_mat @ g_mat
  | Compose (f, g, _) ->
    let state, g_mat = eval_inner g config state in 
    let state, f_mat = eval_inner f config state in
    state, 
    let+ f_row = f_mat in
    let (action, data) = MatchActionTable.run g_mat f_row.data in 
    MatchAction.{f_row with action;data}
  | MapOut (f, tfx, _) ->
    let state, mat = eval_inner f config state in
    List.fold mat ~init:(state, []) 
      ~f:(fun (state, mat) row -> 
        let state, rows = apply_out_tfx state row tfx in
        (state, mat @ [rows])
      )
  | MapIn (f, tfx, _) ->
    let state, f_mat = eval_inner f config state in 
    state,
    let* f_row = f_mat in
    apply_in_tfx f_row tfx

let eval_ clause config = 
  NonceState.empty
  |> eval_inner clause config
  |> snd

(* Execute a list of BaseLogic Clauses step by step *)
let eval_program (initial_config : Config.t) (program : BaseLogic.t list) :
    (string * MatchActionTable.t) list * Config.t =
  let execute_step (current_config, accumulated_results) step =
    let result_table = eval_ step.definition current_config in
    let new_config =
      BaseLogic.Config.
        {
          symbols = Set.add current_config.symbols (Symbol.to_string step.defined);
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

let eval init prog = 
  let _, out = eval_program init prog in
  Config.diff out init