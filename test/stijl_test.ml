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

module AvTest = struct

  let metadata = v9 "metadata1"
  let eth_dst = v48 "eth.dst"
  let eth_src = v48 "eth.src"
  let eth_dst' = v48 "eth.dst1"
  let eth_src' = v48 "eth.src1"
  let ipv4_dst = v32 "ipv4.dst"
  let ipv4_dst' = v32 "ipv4.dst1"
  let port = v9 "port" 
  let port' = v9 "port1"

  let drop p = Primitives.Action.([], [
      assign p @@ Expr.bvi 511 9
    ])

  let route = Primitives.Action.( [v48 "dmac"; v9 "p"], [
    assign port @@ Expr.var @@ v9 "p";
    assign eth_src @@ Expr.var eth_dst;
    assign eth_dst @@ Expr.var @@ v48 "dmac"])
  let ipv4_route = GPL.table "ipv4_route" [(ipv4_dst, Exact)] [route; drop port]

  let fwd = Primitives.Action.([v9 "p1"], [
    assign port' @@ Expr.var @@ v9 "p1"
  ])
  let ipv4_fwd = GPL.table "ipv4_fwd" [(ipv4_dst', Exact)] [fwd; drop port']

  let rewrite = [v48 "dmac1"], Primitives.Action.[
    assign eth_src' @@ Expr.var eth_dst';
    assign eth_dst' @@ Expr.var @@ v48 "dmac1";
  ]
  let ipv4_rewrite = GPL.(
    table "ipv4_rewrite" [(ipv4_dst', Exact)] [
      rewrite; ([],[])
    ])

  let seq (params1, acts1)  (params2, acts2) =
    (params1 @ params2, acts1 @ acts2)

  let set_metadata = Primitives.Action.([v9 "m1"], [
    assign metadata @@ Expr.var @@ v9 "m1"
  ])

  let lag = 
    GPL.table "aggregate" [(ipv4_dst', Exact)] [
      set_metadata 
    ]

  let next = 
    GPL.table "next" [(metadata, Exact)] [
      seq fwd rewrite;
      drop port'
    ]
    

  let abstract = ipv4_route
  let decompose = GPL.(sequence [ipv4_fwd; ipv4_rewrite])
  let metadata = GPL.(sequence [lag; next])

  let equality = 
    let open BExpr in 
    let open Expr in 
     ands [
      var ipv4_dst == var ipv4_dst';
      var eth_dst == var eth_dst';
      var eth_src == var eth_src';
      var port == var port'
    ]


  let metadata_decompose test () = 
    let abs_funs, tgt_funs, is_correct = 
      BExpr.(Expr.(ands [var eth_src == var eth_src']))
      |> TopDownEnum.init_search equality abstract metadata  
    in 
    let x = Var.make "x" 32 in 
    (* let p = Var.make "p" 9 in *)
    let doroute = Var.make "Ipv4_route$action" 2 in 
    let ipv4_port = Var.make "Ipv4_route$data$p" 9 in
    let ipv4_dmac = Var.make "Ipv4_route$data$dmac" 48 in 
    let donext = Var.make "Next$action" 2 in 
    let next_port = Var.make "Next$data$p1" 9 in 
    let next_dmac = Var.make "Next$data$dmac1" 48 in 
    let meta = Var.make "Aggregate$data$m1" 9 in 
    let solution =
      let open BExpr in
      let open Expr in 
      ands [
        (meta $ var x) == (ipv4_port $ var x);
        (donext $ (meta $ var x)) == (doroute $ var x);
        (next_port $ (meta $ var x)) == (ipv4_port $ var x);
        (next_dmac $ (meta $ var x)) == (ipv4_dmac $ var x);
      ]
    in
    match test with 
    | `Verif -> 
      BExpr.forall x solution
      |> is_correct 
      |> Alcotest.(check bool) "is correct" true
    | `Mem n -> 
      TopDownEnum.FormGen.ite_synth abs_funs tgt_funs 
      |> Stream.take n
      |> contains solution
    | `Synth n -> 
      TopDownEnum.synthesize n equality abstract metadata equality
      |> found_solution

  let action_decompose test () = 
    let abs_funs, tgt_funs, is_correct = TopDownEnum.init_search equality abstract decompose equality in 
    let x = Var.make "x" 32 in 
    let route = Var.make "Ipv4_route$action" 2 in 
    let rewrite = Var.make "Ipv4_rewrite$action" 2 in
    let fwd = Var.make "Ipv4_fwd$action" 2 in 
    let route_port = Var.make "Ipv4_route$data$p" 9 in 
    let route_dmac = Var.make "Ipv4_route$data$dmac" 48 in
    let fwd_port = Var.make "Ipv4_fwd$data$p1" 9 in 
    let rewrite_dmac = Var.make "Ipv4_rewrite$data$dmac1" 48 in
    let solution =
      let open BExpr in
      let open Expr in 
      ands [
        (rewrite $ var x) == (route $ var x);
        (fwd $ var x) == (route $ var x);
        (fwd_port $ var x) == (route_port $ var x);
        (rewrite_dmac $ var x) == (route_dmac $ var x);
      ]
    in      
    match test with 
    | `Verif -> 
      BExpr.forall x solution
      |> is_correct 
      |> Alcotest.(check bool) "is correct" true
    | `Mem n -> 
      TopDownEnum.FormGen.ite_synth abs_funs tgt_funs 
      |> Stream.take n
      |> contains solution
    | `Synth n -> 
      TopDownEnum.synthesize n equality abstract decompose equality
      |> found_solution
  

end

let basic_identity n () = 
  let p = GPL.table "s" [(v32 "x", Exact)] [
    [v9 "w"], Primitives.Action.[assign (v9 "y") @@ Expr.var @@ v9 "w"];
  ] in
  let q = GPL.table "t" [(v32 "x1", Exact)] [
    [v9 "w1"], Primitives.Action.[assign (v9 "y1") @@ Expr.var @@ v9 "w1"];
  ] in
  let pre = BExpr.(Expr.( var (v32 "x") == var (v32 "x1"))) in 
  let pst = BExpr.(Expr.( var (v9 "y") == var (v9 "y1"))) in
  TopDownEnum.synthesize n pre p q pst
  |> found_solution


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

let two_to_one_verif () = 
  let (pre, p, q, pst, solution) = two_to_one_problem in 
  let _, _, is_correct = TopDownEnum.init_search pre p q pst in
  assert (solution |> is_correct)

let two_to_one_synth n () = 
  let (pre, p, q, pst, _) = two_to_one_problem in 
  TopDownEnum.synthesize n pre p q pst
  |> Option.value_exn
  |> BExpr.to_smtlib
  |> Printf.printf "%s\n%!"

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

let cfgtst = 
  let open DSLv2 in 
  Alcotest.testable 
    (Fmt.of_to_string Config.to_string) 
    (Config.equal)


let equal_output cfg cfg' = 
  Alcotest.(check cfgtst) "equal configuration output" cfg cfg'

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
  
let identity () = 
  let open DSLv2 in 
  (* let cfg = of_aslist [ 
    "S", ["dst"], [
      [Exact (bv32 88)], ("fwd", ["p", bv9 8]);
      [Optional None], ("fwd", ["p", bv9 511])
    ]
  ] in  *)
  let map = Seq [
    copy "Eth'" "Eth";
    copy "IPv4'" "IPv4";
    copy "Validate'" "Validate";
  ] in
  let cfg' = 
    Map.(fold experimental_data ~init:experimental_data ~f:(fun ~key ~data config -> 
      add_exn ~key:(key ^ "'") ~data config)
    )
  in
  run experimental_data map
  |> equal_output cfg'


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


  let two_to_one_exec () = 
    let open DSLv2 in  
(*     let cfg = of_aslist [ 
      "S", ["dst"], [
        [Exact (bv32 88)], ("route", ["p", (bv 8 ~w:9); "dmac", (bv48 8888)]);
        [Exact (bv32 99)], ("route", ["p", bv9 9; "dmac", (bv48 9999)]);
        [Optional None], ("drop", [])
      ]
    ] in  *)
    let map = 
      Seq [
        copy "Eth'" "Eth";
        Assign {table = "Forward"; from = ["IPv4"];
          body = case' "IPv4" [
            "route", Pipe(RenameActionTo "fwd", DataSlice ["p"]);
            "nop", Id
          ];
        };
        Assign {table = "Rewrite"; from = ["IPv4"];
          body = case' "IPv4" [
            "route", Pipe(RenameActionTo "rewrite", DataSlice["dmac"]);
            "nop", Id;
          ]
        };
        copy "Validate'" "Validate";
      ]
    in
    let cfg' = of_aslist [
      "Eth'", ["dmac"], eth_rules;
      "Forward", ["dst"], ipv4_rules |> project_asdata ["p"] |> rename_action ["route", "fwd"];
      "Rewrite", ["dst"], ipv4_rules |> project_asdata ["dmac"] |> rename_action ["route", "rewrite"];
      "Validate'", ["inport"; "smac"; "dmac"; "ethertype"; "src"; "dst"; "ttl"], validate_rules
    ]
    in
    let target_tables = Config.restrict ["Eth'"; "Forward"; "Rewrite"; "Validate'"] in
    target_tables (run experimental_data map)
    |> equal_output (target_tables cfg')

  let reorder () = 
    let open DSLv2 in  
    let open Semantics.Match in 
(*     let cfg = of_aslist [ 
      "S", ["dst"], [
        [Exact (bv32 88)], ("route", ["p", (bv9 8); "dmac", (bv48 8888)]);
        [Exact (bv32 99)], ("route", ["p", (bv9 9); "dmac", (bv48 9999)]);
        [catch_all 32], ("drop", [])
      ];
      "V", ["ttl"], [
        [Ternary Trit.Vector.(zero 7 @ [Trit.U])], ("drop", []);
        (* [Exact (bv8 0)], ("drop", []); *)
        [catch_all 8], ("nop", [])
      ]
      ] in  *)
    let map = 
        Seq [
          copy "Eth'" "Eth";
          copy "IPv4'" "IPv4";
          Assign { table = "Validate'"; from = ["Validate"];
            body = Map(Table "Validate", MapKey ("ttl", ["ttl"], Incr (Var ("ttl",8))))
          }
      ]
    in
    let cfg' = of_aslist [
      "Validate'", ["inport"; "smac"; "dmac"; "ethertype"; "src"; "dst"; "ttl"],
      [  
        [idc 9; idc 48; idc 48; Ternary(tv16 2048); idc 32; idc 32; Ternary(tv8 2)], ("drop", []);
        [idc 9; idc 48; idc 48; Ternary(tv16 2048); idc 32; idc 32; Ternary(tv8 1)], ("drop", []);
        [idc 9; idc 48; idc 48;             idc 16; idc 32; idc 32;          idc 8], ("nop", [])
      ]
    ] in
    run experimental_data map
    |> Config.restrict ["Validate'"]
    |> equal_output cfg'
 
let metadata () =
  let open DSLv2 in 
  let open Semantics.Match in 
  let map = 
      Seq [
        copy "Eth'" "Eth";
        copy "Validate'" "Validate";
        Assign { table = "Agg"; from = ["IPv4"]; 
          body = Map(Table "IPv4",
              Pipe(MapData("g", ["dst"], Fun("Grp", ["dst"], 9)), 
              Pipe(RenameActionTo "lag", DataSlice ["g"])))
        };
        Assign { table = "LAG"; from = ["IPv4"];
          body = Map(Table "IPv4", Pipe(MapKey("grp", ["dst"], Fun("Grp", ["dst"], 9)), KeySlice ["grp"]))
        }
    ]
  in
  let cfg' = of_aslist [
    "Agg", ["dst"], (List.init data_size ~f:(fun i -> 
      [Exact (bv32 i)], ("lag", ["g", (bv9 i)]))
    ) @ [
      [catch_all 32], ("lag", ["g", bv9 data_size])
    ];
    "LAG", ["grp"], (List.init data_size ~f:(fun i -> 
      [Exact (bv9 i)], ("route", ["p", (bv9 i); "dmac", (bv48 i)])
    ) @ [
      [Exact (bv9 data_size)], ("nop", [])
    ])
  ] 
  in
  let target_tables = Config.restrict ["Agg"; "LAG"] in
  target_tables (run experimental_data map)
  |> equal_output cfg'  

  let double () =
    let open DSLv2 in 
    let map = 
        Seq [
          const "Eth1" ["dmac", 48] "drop" [];
          const "IPv41" ["dst", 48] "nop" [];
          const "Validate1"  ["inport", 9; "smac", 48; "dmac", 48; "ethertype", 16; "src", 32; "dst", 32; "ttl", 8] "nop" [];
          copy "Eth2" "Eth";
          copy "IPv42" "IPv4";
          copy "Validate1" "Validate";
          copy "Validate2" "Validate";
      ]
    in
    let cfg' = String.Map.map_keys_exn experimental_data ~f:(fun key -> key ^ "2") in 
    let target_tables = Config.restrict ["Validate2"; "Eth2"; "IPv42"] in
    target_tables (run experimental_data map)
    |> equal_output cfg'  
    
    
let choice () =
    let open DSLv2 in 
    let map = 
        Seq [
          const "Staging" [("inport", 9)] "chose" ["path", bv ~w:1 1];
          const "Eth1" ["dmac", 48] "drop" [];
          const "IPv41" ["dst", 48] "nop" [];
          const "Validate1"  ["inport", 9; "smac", 48; "dmac", 48; "ethertype", 16; "src", 32; "dst", 32; "ttl", 8] "nop" [];
          copy "Eth2" "Eth";
          copy "IPv42" "IPv4";
          copy "Validate1" "Validate";
          copy "Validate2" "Validate";
      ]
    in
    let cfg' = String.Map.map_keys_exn experimental_data ~f:(fun key -> key ^ "2") in 
    let target_tables = Config.restrict ["Validate2"; "Eth2"; "IPv42"] in
    target_tables (run experimental_data map)
    |> equal_output cfg'  
    

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

let simple_encodings  = 
  let open ADD in
  ["11*"; "*"; "*1*"; "**0"]
  |> List.map ~f:(fun tv_str -> 
    begin fun () -> 
      of_matchstring tv_str |> to_ternary
      |> Alcotest.(check @@ pair (list tv) (list tv)) "same sets" ([Trit.Vector.of_string tv_str],[])
    end 
    |> Alcotest.test_case (Printf.sprintf "check round trip of %s" tv_str) `Quick )

let add_paths () = 
  let open ADD in 
  Branch {
    tru = DontCare (Branch {
      tru = Out ("ctrl");
      fls = Out ("drop")
    });
    fls = Branch {
      tru = DontCare (Out ("ctrl"));
      fls = DontCare (Out ("drop"));
    }
  }
  |> get_paths
  |> Alcotest.(check @@ list @@ pair tv string) "paths" Trit.Vector.[
    of_string "1*1", "ctrl";
    of_string "1*0", "drop";
    of_string "01*", "ctrl";
    of_string "00*", "drop"
  ]

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

let incr_is_generated () = 
  let open QueueSearch in 
  let context = String.Map.of_alist_exn Type.[
    "ttl", Var 8;
    "src", Var 32;
    "dst", Var 32
  ] in
  let get_next = rexp_extend context in 
  let candidates = List.(get_next RHole >>= get_next >>= get_next) in 
  let open DSLv2 in 
  let desired = MapKey ("ttl", ["ttl"], Incr (Var ("ttl", 8))) in
  Printf.printf "looking for %s\n%!" (rowexp_to_string desired);
  let f cand = 
    Printf.printf "%s\n%!" (rowexp_to_string cand);
    rowexp_equal cand desired 
  in 
  assert (List.exists candidates ~f);
  Alcotest.(check pass) "finishes without failing" () ()


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
      "Synthesizer", [
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
