open Core
open DSLv2

let bv_one w = SMT.bv 1 w

let rec bv_compile = function
  | BVHole -> failwith "cannot compile holes"
  | Var (x,_) -> SMT.var x
  | Lit bv -> SMT.bv' bv
  | Fun (f, xs, _) -> SMT.symb f (List.map ~f:SMT.var xs)
  | Incr e -> SMT.( + ) [bv_compile e; bv_one (bvexp_width e)]
  | Decr e -> SMT.( - ) [bv_compile e; bv_one (bvexp_width e)]


module ActAbs = struct
  (* Every action is associated with a different bitvector identifier
    we must translate the schemas to assertions about which actions each table is allowed to produce 
  *) 
  type t = string list

  let find_exn acts name =
    List.findi acts ~f:(fun _ -> String.(=) name)
    |> Option.value_exn ~message:("Couldn't find action " ^ name)
    |> Tuple2.get1

  let num_bits acts = 
    (* Certainly enough bits... can minimize using log2 *)
    List.length acts

  let findbv_exn acts name =
    let i = find_exn acts name in 
    let w = num_bits acts in 
    SMT.bv i w

  let of_type_context types =
    Type.get_all_actions types
    |> String.(List.dedup_and_sort ~compare)
end

let action_name tbl_name = Printf.sprintf "%s$action" tbl_name

let symbolic_table types (name : string) =
  let keys = Type.find_keys_exn types name |> List.map ~f:(fun (k, _) -> SMT.var k) in 
  let actvar = SMT.var (action_name name) in 
  SMT.((=) [symb name keys; actvar])

let rec rowexp_compile act_map tbl r phi = 
  match r with 
  | RHole -> failwith "cannot compile hole"
  | Id -> phi
  | RenameActionTo name -> 
    let i = ActAbs.find_exn act_map name in
    let w = ActAbs.num_bits act_map in 
    (* Equivalent to action := idx *)
    SMT.(subst phi (action_name tbl) (bv i w))
  | DataSlice _ | KeySlice _ -> phi
  | MapKey (x, _, e) | MapData (x, _, e) -> 
    SMT.(subst phi x (bv_compile e))
  | Pipe (r1, r2) -> 
    phi
    |> rowexp_compile act_map tbl r2
    |> rowexp_compile act_map tbl r1

let lifted_exp_compile types act_map t e =
  match e with
  | EHole | Case {table=_;callbacks=None}-> failwith "cannot compile expression with hole"
  | Literal _ -> failwith "TODO compile literal MAT"
  | Table s ->
    let s_keys = Type.find_keys_exn types s in
    let t_keys = Type.find_keys_exn types t in 
    assert (List.equal (Tuple2.equal ~eq1:String.equal ~eq2:Int.equal) s_keys t_keys);
    let keys_sorts = List.map s_keys ~f:(fun (x,w) -> (x, SMT.bv_sort w)) in  
    let keys = List.map s_keys ~f:(fun (k,_) -> SMT.var k) in 
    SMT.(forall keys_sorts ((=) [
      symb s keys;
      symb t keys 
    ]
    ))
  | Map (Table s, rowexp) ->
    let pre = symbolic_table types t in 
    let post = symbolic_table types s in 
    SMT.implies [pre; rowexp_compile act_map t rowexp post]
  | Case {table = s; callbacks=Some callbacks} ->
    let pre = symbolic_table types s in 
    let post = symbolic_table types t in
    let s_keys = Type.find_keys_exn types s |> List.map ~f:(fun (k,_) -> SMT.var k) in 
    let is_action idx =
      SMT.((=) [symb s s_keys; idx])
    in
  let cases = String.Map.fold callbacks ~init:[] ~f:(fun ~key:action ~data:rowexp acc -> 
      let idx = ActAbs.findbv_exn act_map action in 
      let phi = rowexp_compile act_map t rowexp post in
      acc @ [SMT.implies [is_action idx; phi]]
    ) in
    SMT.(implies [ pre; and_  cases ])
  | _ -> failwith "Program must be lifted"

let rec lifted_compile types act_map c =
  match c with 
  | Assign {table; from=_; body} ->
    lifted_exp_compile types act_map table body
  | Seq cs -> SMT.and_ (List.map cs ~f:(lifted_compile types act_map))

let function_declarations (types : Type.ctx) act_width =
  String.Map.fold types ~init:[] ~f:(fun ~key:name ~data:typ acc -> 
    match typ with 
    | Table _ -> 
      acc @ [
        let key_sorts = Type.find_keys_exn types name |> List.map ~f:(fun (_,w) -> SMT.bv_sort w) in 
        SMT.(declare_fun name key_sorts (bv_sort act_width))
      ]
    | _ -> 
      acc
  )

let function_specifications (types : Type.ctx) act_map =
  let w = ActAbs.num_bits act_map in 
  String.Map.fold types ~init:[] ~f:(fun ~key:tbl ~data:typ acc -> 
    match typ with 
    | Table tbltype -> 
      let qkeys = Type.find_keys_exn types tbl |> List.map ~f:(fun (x, w) -> x, SMT.bv_sort w)in 
      let key_vars = List.map qkeys ~f:(fun (x,_) -> SMT.var x) in
      let act_ids = List.map tbltype.actions ~f:(ActAbs.find_exn act_map) in 
      let act_is i = SMT.((=) [bv i w; symb tbl key_vars]) in
      acc @ [
        List.map act_ids ~f:act_is
        |> SMT.or_
        |> SMT.forall qkeys
        |> SMT.assert_
      ]
    | _ -> 
      (*tbl is not actually a table*) 
      acc
  )

let constant_declarations (types : Type.ctx) =
  Type.get_vars types 
  |> List.map ~f:(fun (x, w) -> 
    SMT.(declare_const x (bv_sort w))
  )

let preamble_compile types act_map = 
  let act_width = ActAbs.num_bits act_map in 
  let funcs = function_declarations types act_width in 
  let asserts = function_specifications types act_map in 
  let consts = constant_declarations types in 
  funcs @ asserts @ consts

let lifted_check types program spec =
  let act_map = ActAbs.of_type_context types in 
  let preamble = preamble_compile types act_map in
  let compiled = lifted_compile types act_map program in 
  preamble @ SMT.[
    assert_ compiled;
    assert_ (not spec);
  ]

