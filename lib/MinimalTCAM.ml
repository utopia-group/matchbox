open Core
open Semantics

let solver smt = 
  let path = "/usr/bin/z3 -smt2 -in" in
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

let match_to_smt =
  String.Map.fold ~init:([], SMT.true_) ~f:(fun ~key ~data (vars, phi) ->
    let open SMT in
    let w = Match.length data in 
    let v,m = Match.to_mask_pair data in 
    vars @ [key, w], and_ [phi; does_match (var key) (bv' v) (bv' m)]
  )

let matches_to_smt matches =
  List.fold matches ~init:([],SMT.false_) ~f:(fun (xs, phi) m -> 
    let xs', phi' = match_to_smt m in 
    (xs @ xs', SMT.or_ [phi; phi'])
  )


let mask_hole = Printf.sprintf "?%s_mask_%d"

let val_hole = Printf.sprintf "?%s_%d"

let count = Printf.sprintf "$count$"

let match_to_sketch i matches =
  String.Map.fold matches ~init:([], SMT.true_) ~f:(fun ~key ~data (holes, phi) ->
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


let table_to_smt (tbl : MatchActionTable.t) : (string * int) list * ((string * int) list * SMT.expr * SMT.expr) =
  let act_mapping = abstract_actions tbl in
  let avar = "$action" in 
  let anum = length act_mapping in 
  let choose_action aid = SMT.((=) [var avar; bv aid anum]) in 
  let keys = MatchActionTable.keys tbl in
  let n = List.length tbl in  
  let open SMT in 
  (avar, anum) :: keys, (*tables have fixed keys, so we can return the key variables*)
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
  let action = SMT.var "$action" in 
  let action_hole i = Printf.sprintf "?action_%d" i in
  let cases = 
    List.init n ~f:(fun i -> 
    let open SMT in 
    let match_exprs = List.map keys ~f:(fun (key,_) -> 
      let k = var key in 
      let v = var (val_hole key i) in 
      let m = var (mask_hole key i) in 
      does_match k v m
    ) in 
    (and_ match_exprs, (=) [action; var (action_hole i) ]))
  in 
  let phi = 
    List.fold cases ~init:SMT.((=) [action; var (action_hole n)])
      ~f:(fun fls (cond, tru) ->
        SMT.ite cond tru fls
      )
  in 
  let key_vars = List.map keys ~f:(fun (k, w) -> k, SMT.bv_sort w) in 
  let get_holes f = List.bind keys ~f:(fun (key, w) -> List.init (n + 1) ~f:(fun i -> f key i, w)) in 
  let val_holes = get_holes val_hole in 
  let mask_holes = get_holes mask_hole in 
  let action_holes = List.init (n + 1) ~f:(fun i -> (action_hole i, num_acts)) in 
  let declare = List.map ~f:(fun (x, w) -> SMT.(declare_const x (bv_sort w))) in 
  List.concat SMT.[
    declare val_holes;
    declare mask_holes;
    declare action_holes;
    [
      assert_ (forall (("$action", bv_sort num_acts)::key_vars) ((=) [concrete; phi]));
      check_sat;
      get_value (List.map ~f:fst (val_holes @ mask_holes @ action_holes));
    ]
  ]


let remove_shadows (rows : MatchActionTable.t) = 
  List.fold rows ~init:([], []) ~f:(fun (covered, rows') row -> 
    if shadowed covered row.matches then 
      (covered, rows')
    else 
      (covered @ [row.matches], rows' @ [row])
  ) |> snd

let reconstruct tbl tbl_model =
  List.mapi tbl ~f:(fun i row -> 
    MatchAction.{row with 
      matches = String.Map.mapi row.matches ~f:(fun ~key ~data -> 
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
    reconstruct tbl tbl_model
    |> remove_shadows

let minimum_reconstruct n tbl tbl_model =
  let keys = MatchActionTable.keys tbl in 
  let act_mapping =  abstract_actions tbl in 
  List.init (n + 1) ~f:(fun i -> 
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
  )


let minimum_sketch tbl =
  let _, (_, spec, _) = table_to_smt tbl in 
  let n = MatchActionTable.length tbl in 
  let rec loop i = 
    assert (i <= n);
    match solver (table_to_optmt tbl i spec) with 
    | None -> 
      Printf.printf "couldn't solve with %d rules, trying one more" i;
      loop (i + 1)
    | Some tbl_model -> 
      Printf.printf "found a solution iwth %d rows \n%!" i;
      minimum_reconstruct i tbl tbl_model
  in 
  loop 0



let minimize tbl delta =
  (* [tbl] is the minimal element in its equivalence class *)
  (* [delta] is the minimal local update to tbl*)
  let open MatchActionTable in 
  (tbl <+ delta) |> widen
