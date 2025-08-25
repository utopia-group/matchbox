open Core
open BaseLogic

let actions_compat_keys table_type table_type' =
  let open Type in  
  let action_data = get_data table_type in
  let arguments = table_type'.keys in
  String.Map.map arguments ~f:fst
  |> String.Map.equal Int.equal action_data 

let rec match_expr_type ctx e =
  let open MatchTfx in
  match e with 
  | Var x -> 
    Type.find_matchtype_exn ctx x
  | Match m -> 
    Semantics.Match.get_type m
  | AddK (e, bv) | SubK (e, bv) ->
    let w, mk = match_expr_type ctx e in 
    assert (w = Bit.Vector.length bv);
    (w,mk)


let match_tfx_type (ctx : Type.ctx) tfx  (rowtype : (int * Type.match_kind) String.Map.t) : (int * Type.match_kind) String.Map.t =
let open MatchTfx in
  match tfx with 
  | Project vars -> 
    Map.filter_keys rowtype ~f:(List.mem vars ~equal:String.equal)
  | SetTo (x, e) -> 
    Map.set rowtype ~key:x ~data:(match_expr_type ctx e)

let clause_type (ctx : Type.ctx) (clause : Clause.t) = 
  match clause with 
  | Id f -> 
    Type.(Table (find_table_exn ctx f.name))
  | Join (f, g, merge) ->
    let ftype = Type.find_table_exn ctx f.name in
    let gtype = Type.find_table_exn ctx g.name in
    let actions = JoinExp.out_actions merge in 
    assert Type.(JoinExp.wf ftype.actions gtype.actions actions merge);
    Type.(Table {
      keys = merge_keys_exn ftype.keys gtype.keys;
      actions = 
      List.cartesian_product ftype.actions gtype.actions 
      |> List.map ~f:(JoinExp.eval_exn merge)
      ;
      data = union_data_exn ftype.data gtype.data;
    })
  | Compose (f,g) -> 
    let ftype = Type.find_table_exn ctx f.name in
    let gtype = Type.find_table_exn ctx g.name in 
    assert (actions_compat_keys ftype gtype);
    Type.(Table {gtype with keys = ftype.keys})
  | Inverse f -> 
    let ftype = Type.find_table_exn ctx f.name in
    (* Add cispec that f is invertible *)
    Type.(Table (invert_table ftype))

  | MapOut (_,_) ->
    failwith "todo"
  | MapIn (f,tfx) ->
    let tbl = Type.find_table_exn ctx f.name in 
    let in_match_type = tbl.keys in
    let out_match_typ = match_tfx_type ctx tfx in_match_type in
    Type.(Table {tbl with 
      keys = out_match_typ
    })


