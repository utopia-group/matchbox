[@@@warning "-32"]

open Core
open Gpl
open Stijl
(* open Controller_tests *)

(* let cvc5 = "/usr/bin/cvc5 --lang=sygus" *)

let found_solution x = 
  Option.is_some x
  |> Alcotest.(check bool) "found solution" true

let contains phi phis = 
  List.mem phis phi ~equal:BExpr.equal
  |> Alcotest.(check bool) "solution is eventually produced" true


let v32 str = Var.make str 32
(* let v8 str = Var.make str 8 *)
let v9 str = Var.make str 9
let v48 str = Var.make str 48



let two_to_one_problem = 
let p = GPL.table "s" [(v32 "x", Exact)] [
  [v9 "w"], Primitives.Action.[assign (v9 "y") @@ Expr.var @@ v9 "w"];
  [v9 "z"], Primitives.Action.[assign (v9 "y") @@ Expr.var @@ v9 "z"];
] in
let q = GPL.table "t" [(v32 "x1", Exact)] [
  [v9 "w1"], Primitives.Action.[assign (v9 "y1") @@ Expr.var @@ v9 "w1"];
] in
let pre = BExpr.(Expr.( var (v32 "x") == var (v32 "x1"))) in 
let pst = BExpr.(Expr.( var (v9 "y") == var (v9 "y1"))) in
let x = v32 "x" in
let taction = Var.make "T$action" 1 in
let saction = Var.make "S$action" 2 in
let sw = Var.make "S$data$w" 9 in 
let sz = Var.make "S$data$z" 9 in 
let tw = Var.make "T$data$w1" 9 in 
let solution =
  let open BExpr in 
  let open Expr in 
  ands [
    imp [
      (saction $ var x) == bvi 0 2;
      ands [
        (tw $ var x) == (sw $ var x);
        (taction $ var x) == bvi 0 1;
      ]
    ];
    imp [
      (saction $ var x) >= bvi 0 2;
      ands [
        (tw $ var x) == (sz $ var x);
        (taction $ var x) == bvi 0 1;
      ]
    ]
  ]
in 
(pre, p, q, pst, solution)

let of_aslist aslist =
  let open Semantics in 
  List.map aslist ~f:(fun (tbl, matchvars, entries) ->
    Tuple2.create tbl @@ 
    List.map entries ~f:(fun (matches, (name, raw_args)) -> 
      MatchAction.{
        matches = String.Map.of_alist_exn (List.zip_exn matchvars matches); 
        action = Action.{name = name; args = String.Map.of_alist_exn raw_args} 
      }
    )
  )
  |> String.Map.of_alist_exn

let bv v ~w = Bit.Vector.of_int ~width:w v
(* let bv16 = bv ~w:16 *)
let bv32 = bv ~w:32
let bv48 = bv ~w:48
let bv9 =  bv ~w:9
(* let bv8 = bv ~w:8 *)

let tv16 n = bv ~w:16 n |> Trit.Vector.of_bv
let tv8 n = bv ~w:8 n |> Trit.Vector.of_bv

let idc w = Semantics.Match.Ternary (Trit.Vector.wc w)

let data_size = 5

let eth_rules = 
  let open Semantics in 
  let open Match in 
  List.init data_size ~f:(fun i -> 
  [Exact (bv32 i)], ("fwd", ["p", (bv9 (511 - i))]);
) @ [
  [catch_all 32], ("drop", []);
]

let ipv4_rules =
  let open Semantics in
  let open Match in  
  List.init data_size ~f:(fun i -> 
    [Exact (bv32 i)], ("route", ["p", (bv9 i); "dmac", (bv48 i)])
  ) @ [
    [catch_all 32], ("nop", [])
  ]

let validate_rules =
  let open Semantics in 
  let open Trit.Vector in 
  [  
    Match.[idc 9; idc 48; idc 48; Ternary(tv16 2048); idc 32; idc 32; Ternary(zero 7 @ wc 1)], ("drop", []);
          [idc 9; idc 48; idc 48;             idc 16; idc 32; idc 32;                 idc 8], ("nop", [])
  ]

let experimental_data = 
  of_aslist [ 
  "Eth", ["dmac"], eth_rules;
  "IPv4", ["dst"], ipv4_rules;
  "Validate", ["inport"; "smac"; "dmac"; "ethertype"; "src"; "dst"; "ttl"], validate_rules
]

let project_asdata keep = List.map ~f:(fun (matches, (act, data)) -> 
  let data' = List.filter data ~f:(fun (param, _) -> 
    String.(List.mem keep param ~equal)
  ) in 
  (matches, (act, data'))
)

let rename_action subst = 
  let rename old =
    match List.find_map subst ~f:(fun (old', new_) -> if String.(old = old') then Some new_ else None) with 
    | None -> old
    | Some new_ -> new_
  in 
  List.map ~f:(fun (matches, (act, data)) -> 
    (matches, (rename act, data))
  )
    

let vectorset = 
  let open Bit in 
  Alcotest.testable 
    (Fmt.of_to_string VectorSet.to_string)
    (VectorSet.equal)

let bv = 
  let open Bit in 
  Alcotest.testable 
    (Fmt.of_to_string Vector.to_string)
    Vector.equal

let tv = 
  let open Trit in 
  Alcotest.testable
    (Fmt.of_to_string Vector.to_string)
    Vector.equal 

let negation () = 
  let check = Trit.Vector.(eq_pres1 ~f:Bit.Vector.not ~g:not) in
  List.init 1000 ~f:(fun _ -> Random.int 20 |> Trit.Vector.random)
  |> List.find ~f:(fun bs -> not (check bs))
  |> Alcotest.(check (option tv)) "could not find equality violation" None

let check_binary ~f ~g = 
  let check = Trit.Vector.eq_pres2 ~f ~g in
  List.init 100 ~f:(fun _ -> 
    let n = Random.int 4 in
    Trit.Vector.random n, 
    Trit.Vector.random n
  )
  |> List.find ~f:(fun (xs, ys) -> not (check xs ys))
  |> Alcotest.(check (option (pair tv tv))) 
    "could not find equality violation" None


let raw_additions = 
  let open Bit.Vector in 
  [
    "01", "10", "11";
    "000", "000", "000";
    "111", "111", "110";
    "010", "011", "101";
  ]
  |> List.map ~f:(fun (x, y, z) -> 
    let a = of_string x in 
    let b = of_string y in 
    let s = of_string z in 
    Alcotest.test_case (Printf.sprintf "RAW %s + %s = %s" x y z) `Quick 
    (begin fun () -> 
      Alcotest.(check bv) "same bitvector" s Bit.Vector.(a + b)
    end)
  )

let bitwise_and () = check_binary ~f:(Bit.Vector.(&&)) ~g:Trit.Vector.(&&)
let bitwise_or () = check_binary ~f:(Bit.Vector.(||)) ~g:Trit.Vector.(||)
let bitwise_xor () = check_binary ~f:(Bit.Vector.(^)) ~g:Trit.Vector.(^)

let addition () = 
  let open Trit in
  Vector.([F;U;U] + [F; F; U])
  |> Bit.VectorSet.union_map ~f:Vector.denote 
  |> (Bit.VectorSet.cartesian_map (Vector.denote [F; U; U]) (Vector.denote [F; F; U]) ~f:(Bit.Vector.(+))
  |> Alcotest.(check vectorset) "same vectorset")

let overlap () =
  let open Trit in 
  Vector.overlap [F;U;U] [T;U;U]
  |> Alcotest.(check bool) "do overlap, expect true" false

let hex input expected () = 
  Trit.Vector.bitstring_of_hexchar input
  |> Alcotest.(check string) "equivalent bitstrings" expected

let tv_math () =
  let f (tstr, op) = 
    let tv = Trit.Vector.of_string tstr in 
    Intify.realize_operation "x" tv op
    |> List.map ~f:Trit.Vector.to_string
  in
  [
    ("011*", Intify.Exp.(xincr "x"));
    ("01*0", Intify.Exp.(xincr "x"));
  ] |> List.map ~f
    |> Alcotest.(check @@ list @@ list string) "is correct" [
      ["1000"; "0111"];
      ["01*1"];
    ]

(* let rename_slice () =
  let open QueueSearch in 
  let context = String.Map.of_alist_exn Type.[
    "rewrite", Action ["dmac"]; 
    "dmac", Var 48; 
    "fwd", Action ["p"]; 
    "p", Var 9; 
    "nop", Action []] in 
  let get_next = rexp_extend context in 
  let candidates = List.(DSLv2.([RHole] >>= get_next >>= get_next)) in 
  let desired = DSLv2.[
    Pipe(RenameActionTo "fwd", DataSlice ["p"]);
    Pipe(RenameActionTo "rewrite", DataSlice["dmac"]);
    Pipe(RenameActionTo "nop", DataSlice[]);
  ] in
  let f d =
    List.exists candidates ~f:DSLv2.(rowexp_equal d)
  in
  assert (List.for_all desired ~f);
  Alcotest.(check pass) "finishes" () () *)

(* let two_to_one_gen () =
  let open DSLv2 in 
  let sketch =
    case' "S" [
      "route", RHole;
      "drop", RHole;
    ]
  in
  let desired = [
    case' "S" [
      "route", Pipe(RenameActionTo "fwd", DataSlice ["p"]);
      "drop", Id
    ];
    case' "S" [
      "route", Pipe(RenameActionTo "rewrite", DataSlice["dmac"]);
      "drop", Pipe(RenameActionTo "nop", DataSlice[]);
    ]
    ]
  in
  let context = String.Map.of_alist_exn Type.[
    "S", Table {keys = ["dst"]; actions = ["route"; "drop"]};
    "T1", Table {keys = ["dst"]; actions = ["fwd"; "drop"]};
    "T2", Table {keys = ["dst"]; actions = ["rewrite"; "nop"]};
    "dst", Var 32;
    "route", Action ["p"; "dmac"];
    "nop", Action [];
    "fwd", Action ["p"];
    "drop", Action [];
    "rewrite", Action ["dmac"];
    "p", Var 9;
    "dmac", Var 48;
  ] in
  let next = QueueSearch.extend context in 
  let candidates = List.([sketch] >>= next >>= next) in 
  let f d =
    List.exists candidates ~f:(exp_equiv d)
  in
  assert (List.length candidates > 0);
  assert (List.for_all desired ~f);
  Alcotest.(check pass) "finished" () () *)

let minimization () =
  let open Semantics in 
  let table = MatchActionTable.of_alist ["x"] Trit.Vector.[
    [Match.Ternary (of_string "100")], Action.nullary "drop";
    [Match.Ternary (of_string "110")], Action.nullary "drop";
    [Match.Ternary (of_string "011")], Action.nullary "ctrl";
    [Match.Ternary (of_string "010")], Action.nullary "ctrl";
    [Match.Ternary (of_string "001")], Action.nullary "drop";
    [Match.Ternary (of_string "***")], Action.nullary "drop";
  ] in
  let tbl',_ = MinimalTCAM.minimize table in
  Printf.printf "---------------------\n%s\n-----------------------\n%!" (MatchActionTable.to_string tbl');
  assert (MatchActionTable.(length tbl' < 3));
  Alcotest.(check pass) "passing" () ()

let greedy_minimization () =
  let open Semantics in 
  let table = MatchActionTable.of_alist ["x"] Trit.Vector.[
    [Match.Ternary (of_string "100")], Action.nullary "drop";
    [Match.Ternary (of_string "110")], Action.nullary "drop";
    [Match.Ternary (of_string "011")], Action.nullary "ctrl";
    [Match.Ternary (of_string "010")], Action.nullary "ctrl";
    [Match.Ternary (of_string "001")], Action.nullary "drop";
    [Match.Ternary (of_string "***")], Action.nullary "drop";
  ] in 
  let tbl',_ = MinimalTCAM.greedy_minimize table in 
  Printf.printf "---------------------\n%s\n-----------------------\n%!" (MatchActionTable.to_string tbl');
  assert (MatchActionTable.(length tbl' <= 3));
  Alcotest.fail "debugging"

let all_binary_decisions ~nbits () =
  let open Semantics in 
  let num_keys = 
    let open Float in 
    (2. ** (of_int nbits)) - 1.
    |> to_int
  in
  let matches = List.init num_keys ~f:(Bit.Vector.of_int ~width:nbits) in
  let mk_match bits = [Match.Ternary (Trit.Vector.of_bv bits)] in
  let drop = Action.nullary "drop" in 
  let ctrl = Action.nullary "ctrl" in 
  let all_assignments = 
    List.fold matches ~init:([[]]) ~f:(fun all_alignments bits -> 
      List.bind all_alignments ~f:(fun alignment -> 
        [
          alignment @ [mk_match bits, drop];
          alignment @ [mk_match bits, ctrl];
        ] 
      )
    )
  in
  let all_tables =
    List.map all_assignments ~f:(MatchActionTable.of_alist ["x"])
  in 
  let data = 
    List.map all_tables ~f:(fun tbl -> 
      let c = Clock.start () in
      let true_min_table, true_min_num_smt_calls = MinimalTCAM.minimize tbl in 
      let minimize_time = Clock.stop c in 
      let true_min_table_size = MatchActionTable.length true_min_table in 
      let c = Clock.start () in 
      let greedy_min_table, greedy_min_num_smt_calls = MinimalTCAM.greedy_minimize tbl in
      let greedy_min_table_size = MatchActionTable.length greedy_min_table in 
      let greedy_time = Clock.stop c in 
      true_min_table_size, minimize_time, true_min_num_smt_calls,
      greedy_min_table_size, greedy_time, greedy_min_num_smt_calls)
  in
  List.iter data ~f:(fun (m, mt, mc, g, gt, gc) -> 
    Printf.printf "%d,%f,%d,%d,%f,%d\n" m mt mc g gt gc;
  );
  Alcotest.fail "debugging"

let incremental () =
    let open Semantics in 
    let above_rules = MatchActionTable.of_alist ["x"] Trit.Vector.[
      [Match.Ternary (of_string "000")], Action.nullary "drop";
      [Match.Ternary (of_string "011")], Action.nullary "drop"
    ] in 
    let keys = ["x", 3] in 
    let actions = [Action.nullary "drop"; Action.nullary "nop"] in 
    let spec = let open SMT in 
      implies [ 
        or_ [(=) [var "x"; bv 1 3 ]; (=) [var "x"; bv 2 3] ];
        (=) [var "$action"; bv 1 2]]
    in 
    let new_rules = MinimalTCAM.incremental keys actions above_rules spec in 
    Printf.printf "---------------------\n%s\n-----------------------\n%!" (MatchActionTable.to_string new_rules);
    Alcotest.fail "debugging"


let () =
  let open Alcotest in
  run "Stijl"
    [
      (* "Interpreter", [
        test_case "Empty table handling" `Quick Interpreter_tests.test_empty_table;
        test_case "Unrelated clause" `Quick Interpreter_tests.test_unrelated_clause;
        test_case "Id clause" `Quick Interpreter_tests.test_id;
        test_case "Join clause" `Quick Interpreter_tests.test_join;
        test_case "Inverse clause" `Quick Interpreter_tests.test_invert;
        test_case "MapOut Project" `Quick Interpreter_tests.test_mapout_project;
        test_case "MapOut SetTo" `Quick Interpreter_tests.test_mapout_setto;
        test_case "MapIn Project" `Quick Interpreter_tests.test_mapin_project;
        test_case "MapIn SetTo" `Quick Interpreter_tests.test_mapin_setto;
      ]; *)
      (* "Synthesizer", [
        test_case "Id" `Quick Synthesizer_tests.test_id;
        test_case "Compose" `Quick Synthesizer_tests.test_compose;
        test_case "Inverse" `Quick Synthesizer_tests.test_invert;
        test_case "Multiple clause kinds" `Quick Synthesizer_tests.test_multiple_clause_kinds;
        test_case "10-way Compose" `Quick Synthesizer_tests.test_10_way_compose;
        test_case "Join" `Quick Synthesizer_tests.test_join;
        test_case "Join with alignment" `Quick Synthesizer_tests.test_join_with_alignment;
        test_case "Join specific alignments" `Quick Synthesizer_tests.test_join_specific_alignments;
        test_case "Join multi-mapping" `Quick Synthesizer_tests.test_join_multi_mapping;
        test_case "Synthesis variety" `Quick Synthesizer_tests.test_synthesis_variety;
        test_case "MapOut action transformations" `Quick Synthesizer_tests.test_mapout_action_transformations;
        test_case "MapIn match transformations" `Quick Synthesizer_tests.test_mapin_match_transformations;
        test_case "Specific action transformations" `Quick Synthesizer_tests.test_specific_action_transformations;
        test_case "Specific match transformations" `Quick Synthesizer_tests.test_specific_match_transformations;
        test_case "Mixed transformation synthesis" `Quick Synthesizer_tests.test_mixed_transformation_synthesis;
      ]; *)
      "ClassBench parsing", [
        test_case "Parsing ClassBench rules" `Quick Classbench_parsing_tests.test_parsing_classbench_rules;
      ];
      "ACL Translation", [
        test_case "ACL translation typechecks with BaseChecker" `Quick Acl_translation_tests.test_acl_translation_typechecks;
        test_case "ACL translation symbols" `Quick Acl_translation_tests.test_acl_translation_symbols;
      ];
      (* "SurfaceInterpreter", [
        test_case "Transform table symbol" `Quick Surface_interpreter_tests.test_transform_table_symbol;
        test_case "Transform compose" `Quick Surface_interpreter_tests.test_transform_compose;
        test_case "Transform join" `Quick Surface_interpreter_tests.test_transform_join;
        test_case "Transform project" `Quick Surface_interpreter_tests.test_transform_project;
        test_case "Transform invert" `Quick Surface_interpreter_tests.test_transform_invert;
        test_case "Transform filter" `Quick Surface_interpreter_tests.test_filter;
        test_case "Bitvector expressions" `Quick Surface_interpreter_tests.test_bitvec_expressions;
        test_case "TransformExpr to Clause encoding" `Quick Surface_interpreter_tests.test_transform_to_clause_encoding;
        test_case "Filter action constraint" `Quick Surface_interpreter_tests.test_filter_action_constraint;
      ];
      "SurfaceSynthesizer", [
        test_case "Id" `Quick Surface_synthesizer_tests.test_id;
        test_case "Compose" `Quick Surface_synthesizer_tests.test_compose;
        test_case "Inverse" `Quick Surface_synthesizer_tests.test_inverse;
        test_case "Multiple clause kinds" `Quick Surface_synthesizer_tests.test_multiple_clause_kinds;
        test_case "10-way Compose" `Quick Surface_synthesizer_tests.test_10_way_compose;
        test_case "Join" `Quick Surface_synthesizer_tests.test_join;
        test_case "Synthesis variety" `Quick Surface_synthesizer_tests.test_synthesis_variety;
      ] *)
      (* "Controller lifecycle", [
        test_case "switch on/off" `Quick test_switch_lifecycle;
        test_case "link up/down" `Quick test_link_lifecycle;
      ];
      "Controller connectivity", [
        test_case "all-pairs on line" `Quick test_all_pairs_line;
        test_case "all-pairs on ring" `Quick test_all_pairs_ring;
        test_case "unknown packet_in doesn't crash" `Quick
          test_unknown_packet_in_no_crash;
        test_case "no link -> no forward rule" `Quick test_no_link_no_fwd_rule;
      ]; *)
      (* "Verification" , [
        test_case "2Actions->1Act Verif" `Quick two_to_one_verif;
        test_case "Action Decompose Solution" `Quick AvTest.(action_decompose `Verif);
        test_case "Metadata Solution" `Quick AvTest.(metadata_decompose `Verif);
      ]; *)
      (* "Synthesis", [
        test_case "Basic Identity (100)" `Quick (basic_identity 100);
        test_case "2Actions->1Act (100)" `Quick (two_to_one_synth 100);
      ]; *)
      (* "CaseStudies", AvTest.[
        test_case "Action Decompose (1000)" `Quick (action_decompose (`Synth 1000));
        test_case "Metadata Decompose (1000)" `Quick (metadata_decompose (`Synth 1));
      ];
      "DSLRun", [
        test_case "identity mapping" `Quick identity;
        test_case "split_action" `Quick two_to_one_exec;
        test_case "reorder" `Quick reorder;
        test_case "metadata" `Quick metadata;
        test_case "double" `Quick double;
        test_case "choice" `Quick choice;
      ];
      "BitVectors", [
        test_case "negation" `Quick negation;
        test_case "bitwise and" `Quick bitwise_and;
        test_case "bitwise or" `Quick bitwise_or;
        test_case "bitwise xor" `Quick bitwise_xor;
        test_case "addition" `Quick addition;
        test_case "bitwise overlap" `Quick overlap;
      ] @ raw_additions;
      "BDDs", simple_encodings;
      "ADDs", [
        test_case "generate paths" `Quick add_paths
      ];
      "Trits", [
        test_case "hex parsing 0" `Quick (hex '0' "0000");
        test_case "hex parsing 1" `Quick (hex '1' "0001");
        test_case "hex parsing 2" `Quick (hex '2' "0010");
        test_case "hex parsing 3" `Quick (hex '3' "0011");
        test_case "hex parsing 4" `Quick (hex '4' "0100");
        test_case "hex parsing 5" `Quick (hex '5' "0101");
        test_case "hex parsing 6" `Quick (hex '6' "0110");
        test_case "hex parsing 7" `Quick (hex '7' "0111");
        test_case "hex parsing 8" `Quick (hex '8' "1000");
        test_case "hex parsing 9" `Quick (hex '9' "1001");
        test_case "hex parsing a" `Quick (hex 'a' "1010");
        test_case "hex parsing b" `Quick (hex 'b' "1011");
        test_case "hex parsing c" `Quick (hex 'c' "1100");
        test_case "hex parsing d" `Quick (hex 'd' "1101");
        test_case "hex parsing e" `Quick (hex 'e' "1110");
        test_case "hex parsing f" `Quick (hex 'f' "1111");
      ];
      "TVMath",[
        test_case "011* + 1" `Quick tv_math;
      ];
      "RowSynthGen", [
        test_case "ttl = ttl + 1 is generated" `Quick incr_is_generated;
        (* test_case "rename/slice pattern is generated" `Quick rename_slice; *)
      ];
      "DSLv2SynthGen", [
        (* test_case "two-to-one is generated" `Quick two_to_one_gen; *)
      ];
      "Minimization", [
        test_case "2-actions" `Quick minimization;
        test_case "greedy 2-actions" `Quick greedy_minimization;
        test_case "all 6-bit binary decisions" `Quick (all_binary_decisions ~nbits:6);
        test_case "incremental example" `Quick incremental;
      ] *)
    ]
