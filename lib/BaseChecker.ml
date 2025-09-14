open Core
open BaseLogic

let actions_compat_keys table_type table_type' =
  let open Type in  
  let action_data = get_data table_type in
  let arguments = table_type'.keys in
  String.Map.map arguments ~f:fst
  |> String.Map.equal Int.equal action_data 

let rec match_expr_type ctx e =
  let open Gpl.Expr in
  match e with
  | BV (_, w) -> (w, Type.Exact)
  | Var x -> 
    Type.find_matchtype_exn ctx (Var.str x)
  | BinOp(_, e1, e2) ->
    let (w1, mk1) = match_expr_type ctx e1 in 
    let (w2, mk2) = match_expr_type ctx e2 in
    assert (w1 = w2);
    (w1, Type.join mk1 mk2)
  | UnOp (_, e) ->
    match_expr_type ctx e
  | Apply _ -> failwith "[typeof] apply"

let action_expr_type e = Gpl.Expr.width e

let match_tfx_type (ctx : Type.ctx) tfx  (rowtype : (int * Type.match_kind) String.Map.t) : (int * Type.match_kind) String.Map.t =
  let open MatchTfx in
  match tfx with 
  | Del x ->
    Map.remove rowtype (Var.str x)
  | Project vars -> 
    Map.filter_keys rowtype ~f:(fun k -> List.exists vars ~f:(fun x -> String.equal k (Var.str x)))
  | SetTo (x, e) -> 
    Map.set rowtype ~key:(Var.str x) ~data:(match_expr_type ctx e)
  | WildCard x -> 
    Map.set rowtype ~key:(Var.str x) ~data:(Var.width x, LPM)
  | Filter _ -> rowtype
  | CubeFilter _ -> rowtype

let data_tfx_type tfx actions (datatypes : int String.Map.t) : String.Set.t * int String.Map.t = 
  let open ActionTfx in 
  match tfx with 
  | Del x -> 
    actions, Map.remove datatypes (Var.str x)
  | Project vars -> 
    let datatypes' = 
      Map.filter_keys datatypes ~f:(fun k -> List.exists vars ~f:(fun x -> String.equal k (Var.str x)))
    in
    actions, datatypes'
  | SetTo(x, e) ->
    actions, Map.set datatypes ~key:(Var.str x) ~data:(action_expr_type e)
  | Rename (a1,a2) ->
    Set.(add (remove actions a1) a2), datatypes


let rec infer (ctx : Type.ctx) (clause : Clause.t) : Clause.t = 
  let open Semantics in 
  let open Clause in
  match clause with 
  | Id (f, None) -> 
    let typ = Type.(Table (find_table_exn ctx f.name)) in
    Id (f, Some typ)
  | Table (t, _) ->
    let keys = String.Map.of_alist_exn (MatchActionTable.keys t) in 
    let actions = MatchActionTable.action_names t in 
    let data = MatchActionTable.data t in 
    let typ= Type.Table {keys; actions; data} in
    Table (t, Some typ)
  | Join (f, g, None) ->
    let f = infer ctx f in 
    let g = infer ctx g in 
    let ftype = typeof_exn f in
    let gtype = typeof_exn g in
    let typ = let open Type in 
      Table {
        keys = merge_keys_exn ftype.keys gtype.keys;
        actions = 
          List.cartesian_product (Set.to_list ftype.actions) (Set.to_list gtype.actions)
          |> List.map ~f:(fun (a1, a2) -> Printf.sprintf "%s$%s" a1 a2)
          |> String.Set.of_list
        ;
        data = union_data_exn ftype.data gtype.data;
      } in
    Join (f, g, Some typ)
  | Compose (f,g, None) -> 
    let f = infer ctx f in 
    let g = infer ctx g in 
    let ftype = typeof_exn f in
    let gtype = typeof_exn g in
    assert (actions_compat_keys ftype gtype);
    let typ = Type.(Table {gtype with keys = ftype.keys}) in
    Join (f, g, Some typ)
  | MapOut (f, tfx, None) ->
    let f = infer ctx f in 
    let ftype = typeof_exn f in
    let data_types = Type.get_data ftype in  
    let actions = Type.get_actions ftype in 
    let actions, data_types' = data_tfx_type tfx actions data_types in 
    let typ = let open Type in 
      Table {ftype with actions; data = data_types'}
    in
    MapOut(f, tfx, Some typ)
  | MapIn (f,tfx, None) ->
    let f = infer ctx f in 
    let ftype = typeof_exn f in 
    let in_match_type = ftype.keys in
    let out_match_typ = match_tfx_type ctx tfx in_match_type in
    let out = 
      Type.(Table {ftype with 
        keys = out_match_typ
      })
    in
    MapIn(f, tfx, Some out)
  | Id (_, Some _) 
  | Join (_,_, Some _)
  | Compose (_, _, Some _) 
  | MapIn (_, _, Some _)
  | MapOut(_, _, Some _) -> 
    failwith "unexpected type annotation during inference"