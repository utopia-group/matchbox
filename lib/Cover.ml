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
let holes (key : Var.t) : tcam_holes = 
  let name = Var.str key in
  let width = Var.width key in
  { value = Var.make (name ^ "$value") width;
    mask = Var.make (name ^ "$mask") width
  }

let mask key mask = 
  let open SMT in 
  bvand [ var (Var.str key); var (Var.str mask) ]

let hasvalue key v = 
  let open SMT in 
  (=) [ var (Var.str key); bv' v]
   
let make_mask_sketch key bitvector = 
  let open SMT in 
  let h = holes key in
  [h.mask; h.value],
  [key],
  implies [
    hasvalue key bitvector;
    mask key h.mask;
  ]

let widen_sketch hw pkt = 
  match hw with 
  | `TCAM -> 
    Map.fold pkt ~init:([], [], SMT.true_) ~f:(fun ~key ~data (holes, vars, phi) ->
      let kholes, kvars, kphi = make_mask_sketch key data in
      kholes @ holes,
      kvars @ vars, 
      SMT.and_ [kphi; phi]
    )
  | `LPM -> 
    failwith "sketch lpm"

let extract_guard model xs hw : Semantics.Match.t Var.Map.t =
  match hw with
  | `TCAM ->
    let find_bv_exn x = 
      Var.str x 
      |> Map.find_exn model
    in
    List.fold xs ~init:(Var.Map.empty) ~f:(fun guard x -> 
      let h = holes x in 
      let mask = find_bv_exn h.mask in 
      let value = find_bv_exn h.value in
      let tv = Trit.Vector.of_bitmask value mask in
      Map.add_exn guard ~key:x ~data:(Match.Ternary tv)
    )
  | `LPM -> failwith "handle LPM"

let generalize hw prev pkt phi = 
  let holes, vars, sketch = widen_sketch hw pkt in 
  let spec = SMT.(implies [sketch; not prev; phi]) in 
  match maxsolve holes vars spec with
  | None-> failwith "Query should have at least one model, the packet" 
  | Some model ->
    extract_guard model vars hw


let guard_to_smt guard : SMT.expr = 
  let open SMT in 
  Map.fold guard ~init:true_ ~f:(fun ~key ~data acc -> 
    let value, mask = Match.to_mask_pair data in
    SMT.and_ [
      (=) [bvand [var (Var.str key); bv' mask]; bvand [bv' value; bv' mask]];
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

let suffices xs prev phi : Bit.Vector.t Var.Map.t option = 
  suffices_query xs prev phi
  |> solver ~f:Bit.Vector.of_string
  |> Option.map ~f:(Map.fold ~init:Var.Map.empty ~f:(fun ~key ~data -> 
    Map.set ~key:(Var.make key (Bit.Vector.length data)) ~data
  ))

let split_ hw xs (matches : Match.t Var.Map.t) vartheta : Match.t Var.Map.t list = 
  let mu = guard_to_smt matches in 
  let phi = SMT.and_ [mu; vartheta] in
  let rec loop prev (guards : Match.t Var.Map.t list) : Match.t Var.Map.t list =
    match suffices xs prev phi with 
    | None -> 
      guards
    | Some pkt ->
      let guard = generalize hw prev pkt phi in
      let prev = SMT.or_ [guard_to_smt guard; prev] in 
      loop prev (guard::guards)
  in
  loop SMT.true_ []

let split hw matches bexpr = 
  let expr = SMT.of_bexpr bexpr in 
  let xs = Map.keys matches in
  split_ hw xs matches expr