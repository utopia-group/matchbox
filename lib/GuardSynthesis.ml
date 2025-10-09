open Core
open Gpl
open Semantics

let solver ~f smt = 
  let path = "z3 -smt2 -in" in
  SMT.(run (Runner.init path) smt |> check)
  |> Option.map ~f:(Map.map ~f)

let consts (hs : Var.t list) = 
  let hs = List.dedup_and_sort ~compare:Var.compare hs in 
  let open SMT in 
  List.map hs ~f:(fun h -> 
    declare_const (Var.str h) (bv_sort (Var.width h))
  )

let strings = List.map ~f:Var.str

let sort_ed (xs : Var.t list) = 
  List.map xs ~f:(fun x -> Var.str x, SMT.bv_sort (Var.width x))

let ith_bit h i = 
  let open SMT in
  (extract ~hi:i ~lo:i [var (Var.str h)])

let minimize_all_bits holes = 
  List.bind holes ~f:(fun h -> 
    List.init (Var.width h) ~f:(fun i -> 
        SMT.(minimize (ith_bit h i))
      )
  )

let maxsolve_query holes xs (spec : SMT.expr) : SMT.program =
  let open SMT in 
  List.concat [
    consts holes;
    [assert_ (forall (sort_ed xs) spec)];
    minimize_all_bits holes;
    [
      check_sat;
      get_value (strings holes)
    ]
  ]

let maxsolve holes xs spec : Bit.Vector.t SMT.Model.t option = 
  maxsolve_query holes xs spec
  |> solver ~f:Bit.Vector.of_string

let get_name i key = 
  match i with 
  | None -> Var.str key
  | Some idx -> 
    Printf.sprintf "%s$%d" (Var.str key) idx

type tcam_holes = {value : Var.t; mask : Var.t}
let make_tcam_holes i (key : Var.t) : tcam_holes = 
  let name = get_name i key in
  let width = Var.width key in
  { value = Var.make (name ^ "$value") width;
    mask = Var.make (name ^ "$mask") width
  }

type lpm_holes = {value : Var.t; shift : Var.t}
let make_lpm_holes i (key : Var.t) : lpm_holes = 
  let name = get_name i key in 
  let width = Var.width key in 
  { value = Var.make (name ^ "$value") width;
    shift = Var.make (name ^ "$shift") width;
  }

type exact_holes = {value : Var.t}
let make_exact_holes i (x : Var.t) : exact_holes =
  let name = get_name i x in 
  let width = Var.width x in 
  {
    value = Var.make (name ^ "$value") width;
  }


let mask key mask = 
  let open SMT in 
  bvand [ var (Var.str key); var (Var.str mask) ]

let hasvalue key v = 
  let open SMT in 
  (=) [ var (Var.str key); bv' v]
   
let make_mask_sketch i key = 
  let open SMT in 
  let h = make_tcam_holes i key in
  [h.value; h.mask],
  [key],
  (=) [
      mask key h.mask;
      mask h.value h.mask;
  ]
  
let shift key shift = 
  let open SMT in 
  bvlshr [ var (Var.str key); var (Var.str shift) ]

let make_shift_sketch i key = 
  let open SMT in 
  let h = make_lpm_holes i key in 
  [h.value; h.shift],
  [key],
  (=) [
      shift key h.shift;
      shift h.value h.shift;
  ]

let make_exact_sketch i x = 
  let open SMT in 
  let h = make_exact_holes i x in 
  [h.value],
  [x],
  (=) [var (Var.str x); var (Var.str h.value)]

let make_action_sketch i tablename actions = 
  let action = Var.make (tablename ^ "$action") (List.length actions) in
  make_exact_sketch i action

let make_sketch hw i = 
  match hw with
  | `TCAM -> make_mask_sketch i
  | `LPM -> make_shift_sketch i
  | `CAM -> make_exact_sketch i

let widen_sketch ?(i = None) hw (xs : Var.t list) = 
  List.fold xs ~init:([], [], SMT.true_)
    ~f:(fun (holes, vars, phi) x ->
        let kholes, kvars, kphi = make_sketch hw i x in
        kholes @ holes,
        kvars @ vars, 
        SMT.and_ [kphi; phi])

let row_sketch hw keys actionvar data prec i =
  let kholes, kvars, keys_sketch = widen_sketch hw keys ~i:(Some i) in
  let dholes, dvars, data_sketch = widen_sketch `CAM data ~i:(Some i) in 
  let aholes, avars, action_sketch = widen_sketch `CAM [actionvar] ~i:(Some i) in
  let guard = let open SMT in 
    and_ [
      not prec; keys_sketch
    ]
  in
  let consq = let open SMT in
    and_ [
      action_sketch; data_sketch
    ]
  in
  keys_sketch,
  List.concat [kholes; dholes; aholes],
  List.concat [kvars; dvars; avars],
  SMT.implies [guard; consq]



let extract_match ?(i = None) hw model x = 
  let find_bv_exn hole = 
    Var.str hole
    |> Map.find_exn model
  in
  match hw with
  | `TCAM ->
    let h = make_tcam_holes i x in 
    let mask = find_bv_exn h.mask in 
    let value = find_bv_exn h.value in
    let tv = Trit.Vector.of_bitmask value mask in
    Match.Ternary tv
  | `LPM ->
    let h = make_lpm_holes i x in 
    let shift = find_bv_exn h.shift in 
    let value = find_bv_exn h.value in
    Match.Lpm (shift, Bit.Vector.to_int value)



let extract_guard model xs hw : MatchExpression.t =
  List.fold xs ~init:(String.Map.empty) ~f:(fun guard x -> 
    Map.add_exn guard ~key:(Var.str x) ~data:(extract_match hw model x)
  )

let encode_model pkt = 
  let open SMT in 
  Map.fold pkt ~init:[]
   ~f:(fun ~key ~data ->
      (=) [ var (Var.str key); bv' data] 
      |> List.cons
   )
  |> and_

let generalize hw prev pkt phi = 
  let xs = Map.keys pkt in 
  let holes, vars, sketch = widen_sketch hw xs in
  let spec = SMT.(and_ [
    implies [encode_model pkt; sketch];
    implies [sketch; not prev; phi]
    ]) 
  in 
  match maxsolve holes vars spec with
  | None-> failwith "Query should have at least one model, the packet" 
  | Some model ->
    extract_guard model vars hw


let guard_to_smt guard : SMT.expr = 
  let open SMT in 
  Map.fold guard ~init:true_ ~f:(fun ~key ~data acc -> 
    let value, mask = Match.to_mask_pair data in
    SMT.and_ [
      (=) [bvand [var (key); bv' mask]; bvand [bv' value; bv' mask]];
      acc
    ]
  )

let val_to_smt valuation : SMT.expr = 
  let open SMT in 
  Map.fold valuation ~init:true_ ~f:(fun ~key ~data acc ->
    SMT.and_[
      (=) [var key; bv' data];
      acc
    ] 
  )

let suffices_query xs psi phi : SMT.program = 
  List.concat SMT.[
    consts xs;
    [assert_ psi; 
     assert_ (not phi);
     check_sat;
     get_value (strings xs)
    ]
  ]

let suffices xs psi phi : Bit.Vector.t Var.Map.t option = 
  suffices_query xs psi phi
  |> solver ~f:Bit.Vector.of_string
  |> Option.map ~f:(Map.fold ~init:Var.Map.empty ~f:(fun ~key ~data -> 
    Map.set ~key:(Var.make key (Bit.Vector.length data)) ~data
  ))

let split_ hw xs (matches : MatchExpression.t) vartheta : MatchExpression.t list = 
  let mu = guard_to_smt matches in 
  let phi = SMT.and_ [mu; vartheta] in
  let rec loop prev (guards : MatchExpression.t list) : MatchExpression.t list =
    match suffices xs prev phi with 
    | None -> 
      guards
    | Some pkt ->
      let guard = generalize hw prev pkt phi in
      let prev = SMT.or_ [guard_to_smt guard; prev] in 
      loop prev (guard::guards)
  in
  loop SMT.true_ []

let check_sat xs matches expr = 
  let mu = guard_to_smt matches in 
  match suffices xs mu expr with 
  | None -> [matches]
  | Some _ -> []

let coerce = function
  | `CAM -> failwith "impossible"
  | `TCAM -> `TCAM
  | `LPM -> `LPM
   

let split (hw : [`CAM | `LPM | `TCAM]) (matches : MatchExpression.t) bexpr : MatchExpression.t list = 
  let expr = SMT.of_bexpr bexpr in 
  let xs = MatchExpression.keysv matches in
  match hw with 
  | `CAM -> 
    check_sat xs matches expr
  | `TCAM | `LPM -> 
    split_ (coerce hw) xs matches expr

let make_cover_sketch hw num_guards xs = 
  List.init num_guards ~f:(fun i -> widen_sketch hw ~i:(Some i) xs)
  |> List.fold ~init:([],[]) ~f:(fun (holes, sketches) (new_holes,_, new_sketch) -> 
      new_holes @ holes,
      new_sketch :: sketches
    )
  
let find_cover_of_size_query hw xs bexpr i : SMT.program =
  let open SMT in 
  let holes, sketches = make_cover_sketch hw i xs in
  List.concat [
    consts holes;
    [assert_ (forall (sort_ed xs) @@
      (=) [bexpr; or_ sketches];
    );
     check_sat;
     get_value (strings holes)
    ];
  ]

let exists_cover_of_size hw xs bexpr i =
  find_cover_of_size_query hw xs bexpr i
  |> solver ~f:Fun.id
  |> Option.is_some


let compute_min_guard_cover_size hw xs bexpr = 
  let can_cover = exists_cover_of_size hw xs bexpr in 
  let rec loop i = 
    if can_cover i then
      i
    else
      loop (i + 1)
  in
  loop 1
  
let cover_size hw bexpr =
  let expr = SMT.of_bexpr bexpr in 
  let xs = BExpr.free_vars bexpr |> Set.to_list in 
  compute_min_guard_cover_size hw xs expr

let equivalent_of_size_query k hw keys avar data phi =
  Printf.eprintf "trying size %d\n%!" k;
  let psi, holes, xs, _ = 
    List.init k ~f:Fn.id
    |> List.fold ~init:(SMT.true_, [],[], SMT.false_) ~f:(fun (psi, holes, vars, prec) i -> 
      let guard, holes', vars', psi' = row_sketch hw keys avar data prec i in
      Printf.eprintf "Row Sketch %s\n%!" (SMT.e_to_string psi');
      SMT.and_ [psi; psi'],
      holes @ holes',
      vars @ vars',
      SMT.or_ [guard; prec]
    ) 
  in
  let open SMT in 
  consts holes @ [
    assert_ (forall (sort_ed xs) @@ (=) [psi; phi] );
    check_sat;
    get_value (strings holes)
  ]


let find_equivalent_of_size k hw keys avar data phi =
  equivalent_of_size_query k hw keys avar data phi
  |> solver ~f:Fun.id


let tickify =
  let open Hardware in function 
  | TCAM -> `TCAM
  | CAM -> `CAM
  | LPM -> `LPM


let encode_table table = 
  let varify = List.map ~f:(fun (x,w) -> Var.make x w) in
  let hw = tickify (MatchActionTable.hw table) in
  let keys = MatchActionTable.keys table |> varify in
  let data = MatchActionTable.data table |> Map.to_alist |> varify in
  let actions = MatchActionTable.actions table in
  let avar = Var.make "action" (List.length actions) in
  let aid action = 
    let i, _ = List.findi_exn actions ~f:(fun _ -> MagmaAction.equal action) in
    SMT.bv i (List.length actions)
  in
  let (_, phi) = 
    List.fold table ~init:(SMT.false_, SMT.true_) ~f:(fun (prec, phi) row -> 
      let open SMT in 
      let guard = guard_to_smt row.matches in
      let data = val_to_smt row.data in
      let action = (=) [var (Var.str avar); aid row.action] in 
      or_ [prec; guard],
      and_ [
        phi; 
        implies [
          and_ [not prec; guard];
          and_ [action; data]
        ]
      ]
    )
  in
  hw, keys, avar, data, phi

let minimum_size_table (table : MatchActionTable.t) = 
  let hw, keys, avar, data, phi = encode_table table in
  let rec loop k = 
    match find_equivalent_of_size k hw keys avar data phi with 
    | None -> loop (k + 1)
    | Some _ -> k
  in
  loop 1

let minimize (config : BaseLogic.Config.t) = 
  BaseLogic.Config.fold config ~init:0 ~f:(fun ~key ~data acc -> 
    Printf.eprintf "minimizing table %s\n%!" key;
    acc + minimum_size_table data  
  )