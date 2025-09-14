open Core
open Semantics

let solver smt = 
  let path = "z3 -smt2 -in" in
  (* let path = "/usr/local/bin/optimathsat" in  *)
  SMT.(run (Runner.init path) smt |> check)

let (=>) (_ : MatchActionTable.t)  (_ : MatchActionTable.t) : bool = failwith "TODO"

let solve holes phi =
  let hole_names = List.map holes ~f:fst in 
  let consts = List.map holes ~f:(fun (c, s) -> SMT.declare_const c s) in 
  let objectives = List.map hole_names ~f:(fun h -> SMT.(minimize (var h))) in
  let smt = List.concat SMT.[
    consts;
    objectives;
    [assert_ phi; 
     check_sat;
     get_value hole_names]
  ] in
  solver smt

let bv_sortify = List.map ~f:(fun (x,w) -> (x, SMT.(bv_sort w)))

let does_match k v m =
  let open SMT in 
  (=) [
    bvand [k; m];
    bvand [v; m]
  ]

let rec abstract_actions : MatchActionTable.t -> Action.t list = function 
  | [] -> []
  | row::rows ->  
    let rst = abstract_actions rows in 
    if Action.(List.mem rst row.action ~equal) then 
      rst
    else 
      row.action :: rst

let length act_mapping =
  List.length act_mapping

let act_id (actions : Action.t list) a =
  List.findi_exn actions ~f:(fun _ -> Action.equal a)
  |> fst

let get_act (actions : Action.t list) i =
  List.nth actions i 
  |> Option.value_exn ~message:(Printf.sprintf "Couldn't find action with index %d" i)


let match_to_smt =
  Map.fold ~init:([], SMT.true_) ~f:(fun ~key ~data (vars, phi) ->
    let open SMT in
    let w = Match.length data in 
    let v,m = Match.to_mask_pair data in 
    vars @ [key, w], and_ [phi; does_match (var key) (bv' v) (bv' m)]
  )

let action_to_smt act_mapping (action : Action.t) =
  let avar = SMT.var "$action" in 
  let anum = length act_mapping in 
  let aid = act_id act_mapping action in 
  SMT.((=) [avar; bv aid anum])

let matches_to_smt matches =
  List.fold matches ~init:([],SMT.false_) ~f:(fun (xs, phi) m -> 
    let xs', phi' = match_to_smt m in 
    (xs @ xs', SMT.or_ [phi; phi'])
  )


let mask_hole = Printf.sprintf "?%s_mask_%d"

let val_hole = Printf.sprintf "?%s_%d"

let act_hole = Printf.sprintf "?action_%d"

let action_var = "$action"

let count = Printf.sprintf "$count$"

let match_to_sketch i matches =
  Map.fold matches ~init:([], SMT.true_) ~f:(fun ~key ~data (holes, phi) ->
    let open SMT in
    let w = Match.length data in 
    let v,_ = Match.to_mask_pair data in 
    let m = mask_hole key i in 
    holes @ [m, w], and_ [phi; does_match (var key) (bv' v) (var m)]
  )

let shadowed matches new_match = 
  let xs, ms = matches_to_smt matches in 
  let ys, m = match_to_smt new_match in 
  let compare (x, _) (y,_) = String.compare x y in 
  let vars = List.dedup_and_sort (ys @ xs) ~compare in
  let open SMT in 
  List.concat [
    List.map vars ~f:(fun (x, w) -> declare_const x (bv_sort w));
    SMT.[
      assert_ m;
      assert_ (not ms);
      check_sat;
    ]
  ] |> solver |> Option.is_none



let table_to_smt (tbl : MatchActionTable.t) : (string * int) list * ((string * int) list * SMT.expr * SMT.expr) =
  let act_mapping = abstract_actions tbl in
  let anum = length act_mapping in 
  let choose_action aid = SMT.((=) [var action_var; bv aid anum]) in 
  let keys = MatchActionTable.keys tbl in
  let n = List.length tbl in  
  let open SMT in 
  (action_var, anum) :: keys, (*tables have fixed keys, so we can return the key variables*)
  List.rev tbl (* reverse iterate through the table for tail recursion *)
  |> List.foldi ~init:([], false_, false_) ~f:(fun idx (holes, phi1, phi2) (row : MatchAction.t)-> 
    let a = act_id act_mapping row.action in 
    let _, concrete = match_to_smt row.matches in 
    let holes', sketch = match_to_sketch Int.(n - idx) row.matches in (* we're iterating backwards, but the indexing wont*)
    holes @ holes',                       (* Accumulate hole variables *)
    ite concrete (choose_action a) phi1,  (* build the sketch *)
    ite sketch (choose_action a) phi2
  )

let table_to_optmt tbl n concrete =
  let keys = MatchActionTable.keys tbl in 
  let action_mapping = abstract_actions tbl in 
  let num_acts = length action_mapping in 
  let action = SMT.var action_var in
  let cases = 
    List.init n ~f:(fun i -> 
    let open SMT in 
    let match_exprs = List.map keys ~f:(fun (key,_) -> 
      let k = var key in 
      let v = var (val_hole key i) in 
      let m = var (mask_hole key i) in 
      does_match k v m
    ) in 
    (and_ match_exprs, (=) [action; var (act_hole i) ]))
  in 
  let phi = 
    List.fold cases ~init:SMT.((=) [action; var (act_hole n)])
      ~f:(fun fls (cond, tru) ->
        SMT.ite cond tru fls
      )
  in 
  let key_vars = List.map keys ~f:(fun (k, w) -> k, SMT.bv_sort w) in 
  let get_holes f = List.bind keys ~f:(fun (key, w) -> List.init (n + 1) ~f:(fun i -> f key i, w)) in 
  let val_holes = get_holes val_hole in 
  let mask_holes = get_holes mask_hole in 
  let action_holes = List.init (n + 1) ~f:(fun i -> (act_hole i, num_acts)) in 
  let declare = List.map ~f:(fun (x, w) -> SMT.(declare_const x (bv_sort w))) in 
  List.concat SMT.[
    declare val_holes;
    declare mask_holes;
    declare action_holes;
    [
      assert_ (forall ((action_var, bv_sort num_acts)::key_vars) ((=) [concrete; phi]));
      check_sat;
      get_value (List.map ~f:fst (val_holes @ mask_holes @ action_holes));
    ]
  ]


let remove_shadows_aux (rows : MatchActionTable.t) = 
  List.fold rows ~init:([], []) ~f:(fun (covered, rows') row -> 
    if shadowed covered row.matches then 
      (covered, rows')
    else 
      (covered @ [row.matches], rows' @ [row])
  )
let remove_shadows rows = remove_shadows_aux rows |> snd


let covered rows = 
  List.map rows ~f:(fun (row : MatchAction.t) -> row.matches)
  |> matches_to_smt

let reconstruct_mask tbl tbl_model =
  List.mapi tbl ~f:(fun i row -> 
    MatchAction.{row with 
      matches = Map.mapi row.matches ~f:(fun ~key ~data -> 
        let h = mask_hole key (i + 1) in 
        let mask_str = 
          SMT.Model.find tbl_model h 
          |> Option.value_exn ~message:("MinimalTCAM.reconstruct: couldn't find " ^ h)
        in 
        let mask = Bit.Vector.of_string mask_str in 
        Match.remask mask data
      )
    }
  )

let widen tbl =
  let vars, (holes, spec, sketch) = table_to_smt tbl in 
  let qvars = bv_sortify vars in 
  let consts = bv_sortify holes in 
  let phi = SMT.(forall qvars ((=) [sketch; spec])) in 
  match solve consts phi with 
  | None -> failwith "ERROR:: couldn't widen table, this should never happen" 
  | Some tbl_model ->
    reconstruct_mask tbl tbl_model
    |> remove_shadows

let reconstruct_row keys act_mapping tbl_model i =
  let matches = List.map keys ~f:(fun (k,_) -> 
    let vi = val_hole k i in 
    let mi = mask_hole k i in 
    let match_value = SMT.Model.find_exn tbl_model vi |> Bit.Vector.of_string in 
    let mask_value = SMT.Model.find_exn tbl_model mi |> Bit.Vector.of_string in 
    (k, Match.Ternary (Trit.Vector.of_bitmask match_value mask_value))
  ) |> String.Map.of_alist_exn in 
  let action =
    let aid = SMT.Model.find_exn tbl_model (Printf.sprintf "?action_%d" i) |> Bit.Vector.of_string |> Bit.Vector.to_int in 
    get_act act_mapping aid
  in 
  MatchAction.{matches; action}


let extract_rows keys act_mapping n tbl_model =
  List.init (n + 1) ~f:(reconstruct_row keys act_mapping tbl_model)

let minimum_reconstruct n tbl tbl_model =
  let keys = MatchActionTable.keys tbl in 
  let act_mapping =  abstract_actions tbl in 
  List.init (n + 1) ~f:(reconstruct_row keys act_mapping tbl_model)


let minimize tbl =
  let _, (_, spec, _) = table_to_smt tbl in 
  let n = MatchActionTable.length tbl in 
  let num_smt_calls = ref 0 in
  let rec loop i = 
    assert (i <= n);
    let result = solver (table_to_optmt tbl i spec) in 
    Int.incr num_smt_calls;
    match result with 
    | None -> 
      Printf.printf "couldn't solve with %d rules, trying one more" i;
      loop (i + 1)
    | Some tbl_model -> 
      Printf.printf "found a solution iwth %d rows \n%!" i;
      minimum_reconstruct i tbl tbl_model
  in 
  let tbl' = loop 0 in 
  tbl', !num_smt_calls




let widen_delta tbl delta =
  (* [tbl] is the minimal element in its equivalence class *)
  (* [delta] is the minimal local update to tbl*)
  let open MatchActionTable in 
  (tbl <+ delta) |> widen

let uncurry f (a, b) = f a b


let misses (candidate : MatchAction.t list) =
  SMT.and_ @@ 
  List.map candidate ~f:(fun row -> 
    SMT.not (snd (match_to_smt row.matches))
  )

let not_shadowed keys candidate new_symbolic_row =
  SMT.(exists keys (
    and_ [misses candidate; new_symbolic_row]
  ))

let refines act_map keys new_symbolic_row spec =
  let open SMT in 
  let act = action_var, bv_sort (length act_map) in 
  let xs = act::keys in 
  forall xs @@
  implies [spec; new_symbolic_row]

let get_new_row act_map keys candidate spec : MatchAction.t =
  let mask_holes = List.map keys ~f:(fun (k, s) -> (mask_hole k 0, s)) in 
  let key_holes = List.map keys ~f:(fun (k, s) -> (val_hole k 0, s)) in
  let mask_hole_exprs = List.map mask_holes ~f:(fun (k, _) -> SMT.var k) in 
  let triples = List.(zip_exn keys (zip_exn mask_holes key_holes)) in
  let new_symbolic_match = SMT.(and_ (List.map triples ~f:(fun ((k,_), ((m,_), (v,_))) -> does_match (var k) (var v) (var m)))) in 
  let new_symbolic_row = SMT.(implies [new_symbolic_match; (=) [var (act_hole 0); var action_var]]) in
  let response = 
    List.(concat SMT.[
      [declare_const (act_hole 0) (bv_sort (length act_map))];
      mask_holes >>| uncurry declare_const;
      key_holes >>| uncurry declare_const;
      [ assert_ (not_shadowed keys candidate new_symbolic_match) ;
        assert_ (refines act_map keys new_symbolic_row spec)];
      mask_hole_exprs >>| minimize;
      [check_sat;
       get_value @@ (act_hole 0 :: (mask_holes >>| fst) @ (key_holes >>| fst))
      ]
    ])
    |> SMT.run (Runner.init "z3 -smt2 -in")
  in 
  let table_model = SMT.check response |> Option.value_exn ~message:("[get_new_row] failed to extract model") in  
  reconstruct_row keys act_map table_model 0

let has_counterexample keys act_map (candidate : MatchAction.t list) spec =
  (* precondition: the free variables of [spec] are [keys], outputing actions in [act_map], and [candidate] is a table from [keys] to [act_map] *) 
  let open SMT in 
  let phi = 
    SMT.and_ @@
    fst @@
    List.fold candidate ~init:([], SMT.true_) ~f:(fun (encoded_rows, reaching) row -> 
      let open SMT in 
      let _,match_condition = match_to_smt row.matches in
      let action_condition = action_to_smt act_map row.action in 
      let encoded_row = implies [and_ [reaching; match_condition]; action_condition] in
      (encoded_rows @ [encoded_row], and_ [reaching; not match_condition] 
    )
    )
  in
  List.(concat [
    map keys ~f:(fun (x, s) -> declare_const x s);
    [ declare_const action_var (bv_sort (length act_map));
      assert_ (not spec);
      assert_ phi;
      check_sat;
      keys >>| fst |> get_value;
    ];
  ]) 
  |> SMT.run (Runner.init "z3 -smt2 -in")
  |> SMT.check


let greedy keys actions spec =
  let num_smt_calls = ref 0 in 
  let rec loop candidate =
    let result = has_counterexample keys actions candidate spec in
    Int.incr num_smt_calls;
    match result with 
    | None -> 
      candidate
    | Some _ -> 
      let delta = get_new_row actions keys candidate spec in 
      Int.incr num_smt_calls;
      candidate @ [delta]
      |> loop
  in 
  let tbl' = loop [] in 
  tbl', !num_smt_calls

let greedy_minimize table =
  let keys = MatchActionTable.keys table |> bv_sortify in 
  let actions = MatchActionTable.actions table |> List.dedup_and_sort ~compare:Action.compare in 
  let spec = 
    let _, (_, phi, _) = table_to_smt table in 
    phi
  in
  greedy keys actions spec

let get_new_rows actions keys n specmkr =
    let num_acts = length actions in 
    let action = SMT.var action_var in
    let cases = 
      List.init (n + 1) ~f:(fun i -> 
      let open SMT in 
      let match_exprs = List.map keys ~f:(fun (key,_) -> 
        let k = var key in 
        let v = var (val_hole key i) in 
        let m = var (mask_hole key i) in 
        does_match k v m
      ) in 
      (and_ match_exprs, (=) [action; var (act_hole i) ]))
    in 
    let phi = 
      let open SMT in 
      fst @@
      List.fold cases ~init:(true_, [])
        ~f:(fun (phi, cover) (cond, action) ->
          (and_ [phi; implies [and_ cover; cond; action]],
            cover @ [not cond]
          )
        )
    in 
    let key_vars = List.map keys ~f:(fun (k, w) -> k, SMT.bv_sort w) in 
    let get_holes f = List.bind keys ~f:(fun (key, w) -> List.init (n + 1) ~f:(fun i -> f key i, w)) in 
    let val_holes = get_holes val_hole in 
    let mask_holes = get_holes mask_hole in 
    let action_holes = List.init (n + 1) ~f:(fun i -> (act_hole i, num_acts)) in 
    let declare = List.map ~f:(fun (x, w) -> SMT.(declare_const x (bv_sort w))) in 
    List.concat SMT.[
      declare val_holes;
      declare mask_holes;
      declare action_holes;
      [
        assert_ (forall ((action_var, bv_sort num_acts)::key_vars) (specmkr phi));
        check_sat;
        get_value (List.map ~f:fst (val_holes @ mask_holes @ action_holes));
      ]
    ] |> solver
    |> Option.map ~f:(extract_rows keys actions n)

let incremental keys actions 
    above_rules (* the rules above *)
    change_spec (* specification of the incremental change*)
  =
  (* Compute a list of rules, satisfying *)
  (* (1) delta /\ ~match(above) <=> change_spec, and *)
  let _, covered = covered above_rules in 
  let specmkr delta =
    let open SMT in 
    iff [ 
      and_ [not (covered); change_spec];
      and_ [not (covered); delta];
    ]
  in 
  let rec loop i =
    Printf.printf "incremental loop %d\n%!" i;
    match get_new_rows actions keys i specmkr with 
    | None -> loop (i + 1)
    | Some delta -> 
      delta
  in 
  loop 0