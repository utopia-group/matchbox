open Core
open Primitives
include Cmd.Make (Pipeline)
let assign x e = prim (Active (Active.assign x e))
let active a = prim (Active a)

let table name (keys : (Var.t * Table.kind) list) actions =
  prim (Table {name; keys; actions})

let action_to_gpl (action : Primitives.Action.t List.t) = 
  sequence_map ~f:active action

let rec free_vars = function 
  | Prim (Active (Assign (x, e))) -> 
    Set.add (Expr.vars e) x
  | Prim (Active (Passive (Assert phi))) | Prim ((Active (Passive (Assume phi)))) -> 
    BExpr.free_vars phi
  | Prim (Table {name=_;keys;actions}) -> 
    let open Var.Set in 
    let keys = List.map ~f:(fun (x,_) -> x) keys in 
    union_list [
      of_list keys;
      union_list @@ List.map actions ~f:(fun (args, action) -> 
        Set.diff (free_vars (action_to_gpl action)) (of_list args))
    ]
  | Seq cs | Choice cs -> 
    Var.Set.union_list @@ List.map ~f:free_vars cs