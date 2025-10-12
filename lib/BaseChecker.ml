open Core
open BaseLogic

let actions_compat_keys ~first ~second =
  let open Type in  
  let arguments = get_data first in
  let parameters = second.keys in
  String.Map.equal Int.equal 
    arguments parameters

let rec match_expr_type match_type e : int =
  let open Gpl.Expr in
  match e with
  | BV (_, w) -> w (*, Type.Exact)*)
  | Var x -> 
    (* fst (Type.find_matchtype_exn ctx (Var.str x)) *)
    Map.find_exn match_type (Var.str x)
  | BinOp(_, e1, e2) ->
    let w1 = match_expr_type match_type e1 in 
    let w2 = match_expr_type match_type e2 in
    assert (w1 = w2);
    w1(*, Type.join mk1 mk2*)
  | UnOp (_, e) ->
    match_expr_type match_type e
  | Apply _ -> failwith "[typeof] apply"

let rec action_expr_infer datatypes e : Gpl.Expr.t * int =
  let open Gpl.Expr in 
  match e with 
  | Var x -> 
    let name = Var.str x in 
    let w = Map.find_exn datatypes name in 
    Var (Var.make name w), w
  | BV (_, w) -> e, w
  | UnOp (op, e) ->
    let e,w = action_expr_infer datatypes e in 
    UnOp (op, e), w
  | BinOp (bop, e1, e2) -> 
    let e1, w1 = action_expr_infer datatypes e1 in 
    let e2, w2 = action_expr_infer datatypes e2 in
    assert (w1 = w2);
    BinOp (bop, e1, e2), w1
  | Apply _ -> failwith "[action_expr_infer] apply"


let match_tfx_type (_ctx : Type.ctx) tfx  (rowtype : int String.Map.t) : int String.Map.t =
  let open MatchTfx in
  match tfx with 
  | Del x ->
    Map.remove rowtype (Var.str x)
  | Project vars -> 
    Map.filter_keys rowtype ~f:(fun k -> List.exists vars ~f:(fun x -> String.equal k (Var.str x)))
  | SetTo (x, e) -> 
    Map.set rowtype ~key:(Var.str x) ~data:(match_expr_type rowtype e)
  | WildCard x -> 
    Map.set rowtype ~key:(Var.str x) ~data:(Var.width x)
  | Filter _ -> rowtype
  | CubeFilter _ -> rowtype

let data_tfx_type tfx (actions : Type.ActionSet.t) (datatypes : int String.Map.t) : OutTfx.t * Type.ActionSet.t * int String.Map.t = 
  let open OutTfx in 
  match tfx with
  | Nonce x -> 
    assert (Var.width x > 0);
    Nonce x, actions, Map.set datatypes ~key:(Var.str x) ~data:(Var.width x)
  | Del x ->
    let name = Var.str x in 
    let w = Map.find_exn datatypes name in 
    Del (Var.make name w), actions, Map.remove datatypes name
  | Project vars -> 
    let datatypes' = 
      Map.filter_keys datatypes ~f:(fun k -> List.exists vars ~f:(fun x -> String.equal k (Var.str x)))
    in
    let vars' = 
      List.map vars ~f:(fun x -> 
        let name = Var.str x in 
        let w = Map.find_exn datatypes name in 
        Var.make name w
      )
    in
    Project vars', actions, datatypes'
  | SetTo(x, e) ->
    let name = Var.str x in 
    let e,w = action_expr_infer datatypes e in 
    SetTo(Var.make name w, e),
    actions, 
    Map.set datatypes ~key:name ~data:w
  | Rename (a1,a2) ->
    Rename (a1,a2),
    Set.(add (remove actions a1) a2), 
    datatypes
  | Add a ->
    Add a,
    Set.add actions a, 
    datatypes


let rec infer (ctx : Type.ctx) (clause : Clause.t) : Clause.t = 
  let open Semantics in 
  let open Clause in
  match clause with 
  | Id (f, None) -> 
    let typ = Type.(Table (find_table_exn ctx f.name)) in
    Id (f, Some typ)
  | Table (name, t, _) ->
    let keys = String.Map.of_alist_exn (MatchActionTable.keys t) in 
    let actions = Type.ActionSet.of_list (MatchActionTable.action_names t) in 
    let typ_actions = Type.get_table_actions ctx name in
    assert (Set.is_subset actions ~of_:typ_actions);
    let data = MatchActionTable.data t in 
    let hw = MatchActionTable.hw t in 
    let typ = Type.Table {hw; keys; actions = typ_actions; data} in
    Table (name, t, Some typ)
  | Join (f, g, None) ->
    let f = infer ctx f in 
    let g = infer ctx g in 
    let ftype = typeof_exn f in
    let gtype = typeof_exn g in
    let typ = let open Type in 
      Table {
        hw = Hardware.join ftype.hw gtype.hw;
        keys = merge_keys_exn ftype.keys gtype.keys;
        actions = 
          Type.action_product ftype.actions gtype.actions
        ;
        data = union_data_exn ftype.data gtype.data;
      } in
    Join (f, g, Some typ)
  | Override (f, g, _) ->
    let f = infer ctx f in 
    let g = infer ctx g in 
    let ftype = typeof_exn f in
    let gtype = typeof_exn g in
    assert (Type.compare_table ftype gtype = 0);
    Override (f, g, Some (Table ftype))
  | Compose (first, second, None) ->  (* diagram order, i.e second o first*)
    let first = infer ctx first in 
    let second = infer ctx second in 
    let type1 = typeof_exn first in
    let type2 = typeof_exn second in
    assert (actions_compat_keys ~first:type1 ~second:type2);
    let typ = Type.(Table {
      hw = type1.hw;
      keys = type1.keys;
      actions = type2.actions;
      data = type2.data;
    }) in
    Compose (first, second, Some typ)
  | MapOut (f, tfx, None) ->
    let f = infer ctx f in 
    let ftype = typeof_exn f in
    let data_types = Type.get_data ftype in  
    let actions = Type.get_actions ftype in 
    let tfx, actions, data_types' = data_tfx_type tfx actions data_types in 
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