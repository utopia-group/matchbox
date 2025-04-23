open Core
open Gpl
open Stijl

(* let cvc5 = "/usr/bin/cvc5 --lang=sygus" *)

let found_solution x = 
  Option.is_some x
  |> Alcotest.(check bool) "found solution" true

let contains phi phis = 
  List.mem phis phi ~equal:BExpr.equal
  |> Alcotest.(check bool) "solution is eventually produced" true


let v32 str = Var.make str 32
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


let identity_mapping () = 
  let open DSLv2 in 
  let cfg = of_aslist [ 
    "S", ["dst"], [
      [Exact 88], ("fwd", ["p", 8]);
      [Optional None], ("fwd", ["p", 511])
    ]
  ] in 
  let map = Assign {table = "T"; from = ["S"];
                    body = Table "S";
                  }
  in
  let cfg' = of_aslist [
    "S", ["dst"], [
      [Exact 88], ("fwd", ["p", 8]);
      [Optional None], ("fwd", ["p", 511])
    ];
    "T", ["dst"], [
      [Exact 88], ("fwd", ["p", 8]);
      [Optional None], ("fwd", ["p", 511])
    ]
  ] in
  run cfg map
  |> equal_output cfg'


  let two_to_one_exec () = 
    let open DSLv2 in  
    let cfg = of_aslist [ 
      "S", ["dst"], [
        [Exact 88], ("route", ["p", 8; "dmac", 8888]);
        [Exact 99], ("route", ["p", 9; "dmac", 9999]);
        [Optional None], ("drop", [])
      ]
    ] in 
    let map = 
        Seq [
          Assign {table = "T1"; from = ["S"];
            body = Case { 
              table = Table "S"; 
              callbacks = String.Map.of_alist_exn
                ["route", Pipe(RenameActionTo "fwd", DataSlice ["p"]);
                "drop", Id];}
          };
          Assign {table = "T2"; from = ["S"];
            body = Case {
              table =  Table "S";
              callbacks = String.Map.of_alist_exn
                [ "route", Pipe(RenameActionTo "rewrite", DataSlice["dmac"]);
                  "drop", Pipe(RenameActionTo "nop", DataSlice[]);
                ];
            };
          }
      ]
    in
    let cfg' = of_aslist [
      "S", ["dst"], [
        [Exact 88], ("route", ["p", 8; "dmac", 8888]);
        [Exact 99], ("route", ["p", 9; "dmac", 9999]);
        [Optional None], ("drop", [])
      ];
      "T1", ["dst"], [
        [Exact 88], ("fwd", ["p", 8]);
        [Exact 99], ("fwd", ["p", 9]);
        [Optional None], ("drop", [])
      ];
      "T2", ["dst"], [
        [Exact 88], ("rewrite", ["dmac", 8888]);
        [Exact 99], ("rewrite", ["dmac", 9999]);
        [Optional None], ("nop", [])
      ]
    ] in
    run cfg map
    |> equal_output cfg' 

  let reorder () = 
    let open DSLv2 in  
    let cfg = of_aslist [ 
      "S", ["dst"], [
        [Exact 88], ("route", ["p", 8; "dmac", 8888]);
        [Exact 99], ("route", ["p", 9; "dmac", 9999]);
        [Optional None], ("drop", [])
      ];
      "V", ["ttl"], [
        [Exact (-1)], ("drop", []);
        [Exact 0], ("drop", []);
        [Optional None], ("nop", [])
      ]
    ] in 
    let map = 
        Seq [
          Assign { table = "T"; from = ["S"]; body = Table "S" };
          Assign { table = "V'"; from = ["V"];
            body = Map(Table "V", MapKey ("ttl", ["ttl"], Incr (Var "ttl")))
          }
      ]
    in
    let cfg' = of_aslist [
      "S", ["dst"], [
        [Exact 88], ("route", ["p", 8; "dmac", 8888]);
        [Exact 99], ("route", ["p", 9; "dmac", 9999]);
        [Optional None], ("drop", [])
      ];
      "V", ["ttl"], [
        [Exact (-1)], ("drop", []);
        [Exact 0], ("drop", []);
        [Optional None], ("nop", [])
      ];
      "V'", ["ttl"], [
        [Exact 0], ("drop", []);
        [Exact 1], ("drop", []);
        [Optional None], ("nop", [])
      ];
      "T", ["dst"], [
        [Exact 88], ("route", ["p", 8; "dmac", 8888]);
        [Exact 99], ("route", ["p", 9; "dmac", 9999]);
        [Optional None], ("drop", [])
      ];
    ] in
    run cfg map
    |> equal_output cfg' 

let ternary = 
  let open BitVector in
  Alcotest.testable 
    (Fmt.of_to_string Ternary.to_string)
    (Ternary.equal)  
let negation () = 
  let check = BitVector.(eq_pres1 ~f:BitVector.not ~g:not) in
  List.init 100 ~f:(fun _ -> Random.int 4 |> BitVector.random)
  |> List.find ~f:(fun bs -> not (check bs))
  |> Alcotest.(check (option (list ternary))) "could not find equality violation" None

let check_binary ~f ~g = 
  let check = BitVector.eq_pres2 ~f ~g in
  List.init 100 ~f:(fun _ -> 
    let n = Random.int 4 in
    BitVector.random n, 
    BitVector.random n
  )
  |> List.find ~f:(fun (xs, ys) -> not (check xs ys))
  |> Alcotest.(check (option (pair (list ternary) (list ternary)))) 
    "could not find equality violation" None



let bitwise_and () = BitVector.(check_binary ~f:(BitVector.(&&)) ~g:(&&))
let bitwise_or () = BitVector.(check_binary ~f:(BitVector.(||)) ~g:(||))
let bitwise_xor () = BitVector.(check_binary ~f:(BitVector.(^)) ~g:(^))

let () =
  let open Alcotest in 
  run "Stijl" [
    "Verification" , [
      test_case "2Actions->1Act Verif" `Quick two_to_one_verif;
      test_case "Action Decompose Solution" `Quick AvTest.(action_decompose `Verif);
      test_case "Metadata Solution" `Quick AvTest.(metadata_decompose `Verif);
    ];
    "Synthesis", [
      test_case "Basic Identity (100)" `Quick (basic_identity 100);
      test_case "2Actions->1Act (100)" `Quick (two_to_one_synth 100);
    ];
    "CaseStudies", AvTest.[
      test_case "Action Decompose (1000)" `Quick (action_decompose (`Synth 1000));
      test_case "Metadata Decompose (1000)" `Quick (metadata_decompose (`Synth 1));
    ];
    "DSL", [
      test_case "identity mapping" `Quick identity_mapping;
      test_case "split_action" `Quick two_to_one_exec;
      test_case "reorder" `Quick reorder;
    ];
    "BitVectors", [
      test_case "negation" `Quick negation;
      test_case "bitwise and" `Quick bitwise_and;
      test_case "bitwise or" `Quick bitwise_or;
      test_case "bitwise xor" `Quick bitwise_xor;
    ]
  ]