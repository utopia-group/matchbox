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

type tcam_holes = {value : Var.t; mask : Var.t}
let make_tcam_holes (key : Var.t) : tcam_holes = 
  let name = Var.str key in
  let width = Var.width key in
  { value = Var.make (name ^ "$value") width;
    mask = Var.make (name ^ "$mask") width
  }

type lpm_holes = {value : Var.t; shift : Var.t}
let make_lpm_holes (key : Var.t) : lpm_holes = 
  let name = Var.str key in 
  let width = Var.width key in 
  { value = Var.make (name ^ "$value") width;
    shift = Var.make (name ^ "$shift") width;
  }

let mask key mask = 
  let open SMT in 
  bvand [ var (Var.str key); var (Var.str mask) ]

let hasvalue key v = 
  let open SMT in 
  (=) [ var (Var.str key); bv' v]
   
let make_mask_sketch key = 
  let open SMT in 
  let h = make_tcam_holes key in
  [h.value; h.mask],
  [key],
  (=) [
      mask key h.mask;
      mask h.value h.mask;
  ]
  
let shift key shift = 
  let open SMT in 
  bvlshr [ var (Var.str key); var (Var.str shift) ]

let make_shift_sketch key = 
  let open SMT in 
  let h = make_lpm_holes key in 
  [h.value; h.shift],
  [key],
    (=) [
      shift key h.shift;
      shift h.value h.shift;
  ]

let make_sketch hw= 
  match hw with
  | `TCAM -> make_mask_sketch
  | `LPM -> make_shift_sketch

let widen_sketch hw pkt = 
  Map.fold pkt ~init:([], [], SMT.true_)
   ~f:(fun ~key ~data:_ (holes, vars, phi) ->
      let kholes, kvars, kphi = make_sketch hw key in
      kholes @ holes,
      kvars @ vars, 
      SMT.and_ [kphi; phi])

let extract_match hw model x = 
  let find_bv_exn hole = 
    Var.str hole
    |> Map.find_exn model
  in
  match hw with
  | `TCAM ->
    let h = make_tcam_holes x in 
    let mask = find_bv_exn h.mask in 
    let value = find_bv_exn h.value in
    let tv = Trit.Vector.of_bitmask value mask in
    Match.Ternary tv
  | `LPM ->
    let h = make_lpm_holes x in 
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
  let holes, vars, sketch = widen_sketch hw pkt in
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