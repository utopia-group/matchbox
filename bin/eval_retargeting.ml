[@@@warning "-32"]

open Core
open Stijl
open BaseLogic
open Semantics
open Utils

let logical_schema =
  [
    ( "ipv4",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "port"]); ("nop", [])] );
    ("ethernet", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
  ]

let action_decompose_schema =
  [
    ("ipv4_fib", ["hdr.ipv4.dstAddr"], [("ipv4_forward", ["port"]); ("nop", [])]);
    ( "ipv4_rewrite",
      ["hdr.ipv4.dstAddr"],
      [("rewrite", ["dstAddr"]); ("nop", [])] );
    ("ethernet", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
  ]

let choice_schema =
  [
    ( "staging",
      ["standard_metadata.ingress_port"],
      [("set_choice", ["c"]); ("skip_pipe", [])] );
    ( "ipv4",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "port"]); ("nop", [])] );
    ( "ipv42",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "port"]); ("nop", [])] );
    ("ethernet", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ("ethernet2", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
    ( "punt2",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
  ]

let double_schema =
  [
    ( "ipv4",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "port"]); ("nop", [])] );
    ( "ipv42",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "port"]); ("nop", [])] );
    ("ethernet", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ("ethernet2", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
    ( "punt2",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
  ]

let early_validate_schema =
  [
    ( "ethernet_validate",
      ["hdr.ethernet.etherType"; "hdr.ipv4.isValid()"; "hdr.ipv4.ttl"],
      [("malformed", []); ("ok", [])] );
    ( "ipv4_validate",
      ["hdr.ipv4.version"; "hdr.ipv4.ttl"],
      [("malformed", []); ("ok", [])] );
    ( "ipv4",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "port"]); ("nop", [])] );
    ("ethernet", ["hdr.ethernet.dstAddr"], [("eth_fwd", ["port"]); ("nop", [])]);
    ( "acl",
      [
        "hdr.ethernet.srcAddr";
        "hdr.ethernet.dstAddr";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
      ],
      [("drop", [])] );
  ]

let link_agg_schema =
  [
    (* ("lookup", ["port"; "meta.nexthop"], ["nexthop"; "port"]); *)
    ("nexthop", ["meta.nexthop"], [("set_port", ["port"]); ("drop", [])]);
    ( "ethernet",
      ["hdr.ethernet.dstAddr"],
      [("eth_fwd", ["nexthop"]); ("nop", [])] );
    ( "ipv4",
      ["hdr.ipv4.dstAddr"],
      [("ipv4_forward", ["dstAddr"; "nexthop"]); ("nop", [])] );
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [("drop", [])] );
  ]

let ethernet = Symbol.make "ethernet" [] 0
let ipv4 = Symbol.make "ipv4" [] 0
let punt = Symbol.make "punt" [] 0
let ipv4_fib = Symbol.make "ipv4_fib" [] 0
let ipv4_rewrite = Symbol.make "ipv4_rewrite" [] 0

(* logical.p4 to action_decompose.p4 *)

let ipv4_to_ipv4_fib : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "port" 9])

let ipv4_to_ipv4_rewrite : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let logical_to_action_decompose_tfxs : t list =
  [
    {defined = ipv4_fib; definition = ipv4_to_ipv4_fib};
    {defined = ipv4_rewrite; definition = ipv4_to_ipv4_rewrite};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = punt; definition = Clause.id punt};
  ]

(* logical.p4 to choice.p4 *)

let staging = Symbol.make "staging" [] 0
let ethernet2 = Symbol.make "ethernet2" [] 0
let ipv42 = Symbol.make "ipv42" [] 0
let punt2 = Symbol.make "punt2" [] 0

let create_staging : Clause.t =
  Clause.table "staging"
    [
      MatchAction.make TCAM
        (Map.singleton
           (module String)
           "standard_metadata.ingress_port" (Match.catch_all 9))
        (MagmaAction.make "set_choice")
        (Map.singleton (module String) "c" (Bit.Vector.of_int 3 ~width:4));
    ]

let logical_to_choice_tfxs : t list =
  [
    {defined = staging; definition = create_staging};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = ipv42; definition = Clause.id ipv4};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt};
  ]

(* logical.p4 to double.p4 *)

let logical_to_double_tfxs : t list =
  [
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = ipv42; definition = Clause.id ipv4};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt};
  ]

(* logical.p4 to early_validate.p4 *)

let ethernet_validate = Symbol.make "ethernet_validate" [] 0
let ipv4_validate = Symbol.make "ipv4_validate" [] 0
let acl = Symbol.make "acl" [] 0

let punt_to_ethernet_validate : Clause.t =
  Clause.(
    Project
      [
        Var.make "hdr.ethernet.etherType" 16;
        Var.make "hdr.ipv4.isValid()" 1;
        Var.make "hdr.ipv4.ttl" 8;
      ]
    <<| id punt)

let punt_to_ipv4_validate : Clause.t =
  Clause.(
    Project [Var.make "hdr.ipv4.version" 4; Var.make "hdr.ipv4.ttl" 8]
    <<| id punt)

let punt_to_acl : Clause.t =
  Clause.(
    WildCard (Var.make "hdr.ethernet.srcAddr" 32)
    <<| (WildCard (Var.make "hdr.ethernet.dstAddr" 32)
        <<| (Project
               [Var.make "hdr.ipv4.srcAddr" 32; Var.make "hdr.ipv4.dstAddr" 32]
            <<| id punt)))

let logical_to_early_validate_tfxs : t list =
  [
    {defined = ethernet_validate; definition = punt_to_ethernet_validate};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4_validate; definition = punt_to_ipv4_validate};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = acl; definition = punt_to_acl};
  ]

(* logical.p4 to link_agg.p4 *)

let nexthop = Symbol.make "nexthop" [] 0

(* let lookup = Symbol.make "lookup" [] 0 *)

let create_lookup : Clause.t =
  let rec make_unique seen_nexthops nexthop =
    if Set.mem seen_nexthops (Bit.Vector.to_int nexthop) then
      make_unique seen_nexthops (Bit.Vector.incr nexthop)
    else nexthop
  in
  Clause.Table
    ( "lookup",
      Bit.Vector.enumerate 9
      |> List.fold
           ~init:([], Set.empty (module Int))
           ~f:(fun (mas, seen_nexthops) port ->
             let nexthop =
               make_unique seen_nexthops (Bit.Vector.random ~seed:(Some 42) 32)
             in
             ( MatchAction.make TCAM
                 (Map.of_alist_exn
                    (module String)
                    [
                      ("port", Match.Exact port);
                      ("meta.nexthop", Match.Exact nexthop);
                    ])
                 (MagmaAction.make "_")
                 (Map.of_alist_exn
                    (module String)
                    [("port", port); ("nexthop", nexthop)])
               :: mas,
               Set.add seen_nexthops (Bit.Vector.to_int nexthop) ))
      |> fst,
      None )

let lookup_to_nexthop : Clause.t =
  Clause.(
    Project [Var.make "meta.nexthop" 32]
    <<| create_lookup
    |>> Project [Var.make "port" 9])

let ethernet_lookup_to_ethernet : Clause.t =
  Clause.(
    id ethernet
    >>> (Project [Var.make "port" 9]
        <<| create_lookup
        |>> Project [Var.make "nexthop" 32]))

let ipv4_lookup_to_ipv4 : Clause.t =
  Clause.(
    (id ipv4
    >>> (Project [Var.make "port" 9]
        <<| create_lookup
        |>> Project [Var.make "nexthop" 32]))
    * (id ipv4 |>> Project [Var.make "dstAddr" 48]))

let logical_to_link_agg_tfxs : t list =
  [
    (* {defined = lookup; definition = create_lookup}; *)
    {defined = nexthop; definition = lookup_to_nexthop};
    {defined = ethernet; definition = ethernet_lookup_to_ethernet};
    {defined = ipv4; definition = ipv4_lookup_to_ipv4};
    {defined = punt; definition = Clause.id punt};
  ]

(* let ethernet_to_ethernet : Clause.t =
  Clause.(
    id ethernet
    |>> SetTo (Var.make "nexthop" 32, Gpl.Expr.var (Var.make "port" 9)))

let ipv4_to_ipv4 : Clause.t =
  Clause.(
    id ipv4 |>> SetTo (Var.make "nexthop" 32, Gpl.Expr.var (Var.make "port" 9)))

let create_nexthop : Clause.t =
  Clause.table
    (MatchActionTable.of_domain (List.range 1 501) ~hw:TCAM
       ~matches:(fun port ->
         [("nexthop", Match.exact (Bit.Vector.of_int ~width:32 port))])
       ~action:(fun _ -> "set_port")
       ~data:(fun port -> [("port", Bit.Vector.of_int ~width:9 port)]))

let link_agg_tfxs : (string * Clause.t) list =
  [
    ("ethernet", ethernet_to_ethernet);
    ("ipv4", ipv4_to_ipv4);
    ("nexthop", create_nexthop);
    ("punt", Clause.id punt);
  ] *)

(* action_decompose.p4 to logical.p4 *)

let ipv4_fib = Symbol.make "ipv4_fib" [] 0
let ipv4_rewrite = Symbol.make "ipv4_rewrite" [] 0

let ipv4_fib_rewrite_to_ipv4 : Clause.t =
  Clause.(
    id ipv4_fib * id ipv4_rewrite
    |>> Rename
          ( MagmaAction.(make "ipv4_forward" @ make "rewrite"),
            MagmaAction.make "ipv4_forward" ))

let action_decompose_to_logical_tfxs : t list =
  [
    {defined = punt; definition = Clause.id punt};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4; definition = ipv4_fib_rewrite_to_ipv4};
  ]

(* action_decompose.p4 to choice.p4 *)

let action_decompose_to_choice_tfxs : t list =
  [
    {defined = staging; definition = create_staging};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet};
    {defined = ipv4; definition = ipv4_fib_rewrite_to_ipv4};
    {defined = ipv42; definition = ipv4_fib_rewrite_to_ipv4};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt};
  ]

(* action_decompose.p4 to double.p4 *)

let action_decompose_to_double_tfxs : t list =
  [
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet};
    {defined = ipv4; definition = ipv4_fib_rewrite_to_ipv4};
    {defined = ipv42; definition = ipv4_fib_rewrite_to_ipv4};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt};
  ]

(* action_decompose.p4 to early_validate.p4 *)

let punt_to_ipv4_validate : Clause.t =
  Clause.(
    Project [Var.make "hdr.ipv4.version" 4; Var.make "hdr.ipv4.ttl" 8]
    <<| id punt
    |>> Rename (MagmaAction.make "drop", MagmaAction.make "malformed")
    |>> Rename (MagmaAction.make "nop", MagmaAction.make "ok"))

let punt_to_ethernet_validate : Clause.t =
  Clause.(
    Project
      [
        Var.make "hdr.ethernet.etherType" 16;
        Var.make "hdr.ipv4.isValid()" 1;
        Var.make "hdr.ipv4.ttl" 8;
      ]
    <<| id punt
    |>> Rename (MagmaAction.make "drop", MagmaAction.make "malformed")
    |>> Rename (MagmaAction.make "nop", MagmaAction.make "ok"))

let punt_to_acl : Clause.t =
  Clause.(
    WildCard (Var.make "hdr.ethernet.srcAddr" 32)
    <<| (WildCard (Var.make "hdr.ethernet.dstAddr" 32)
        <<| (Project
               [Var.make "hdr.ipv4.srcAddr" 32; Var.make "hdr.ipv4.dstAddr" 32]
            <<| id punt)))

let action_decompose_to_early_validate_tfxs : t list =
  [
    {defined = ethernet_validate; definition = punt_to_ethernet_validate};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4_validate; definition = punt_to_ipv4_validate};
    {defined = ipv4; definition = ipv4_fib_rewrite_to_ipv4};
    {defined = acl; definition = punt_to_acl};
  ]

(* action_decompose.p4 to link_agg.p4 *)

let fib_rewrite_lookup_to_ipv4 : Clause.t =
  Clause.(
    ipv4_fib_rewrite_to_ipv4
    >>> (Project [Var.make "port" 9]
        <<| create_lookup
        |>> Project [Var.make "nexthop" 32]))

let action_decompose_to_link_agg_tfxs : t list =
  [
    {defined = nexthop; definition = lookup_to_nexthop};
    {defined = ethernet; definition = ethernet_lookup_to_ethernet};
    {defined = ipv4; definition = fib_rewrite_lookup_to_ipv4};
    {defined = punt; definition = Clause.id punt};
  ]

(* choice.p4 to logical.p4 *)

let choice_to_logical_tfxs : t list =
  [
    {defined = punt; definition = Clause.id punt};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
  ]

(* choice.p4 to action_decompose.p4 *)

let choice_to_action_decompose_tfxs : t list =
  [
    {defined = ipv4_fib; definition = ipv4_to_ipv4_fib};
    {defined = ipv4_rewrite; definition = ipv4_to_ipv4_rewrite};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = punt; definition = Clause.id punt};
  ]

(* choice.p4 to double.p4 *)

let ethernet2 = Symbol.make "ethernet2" [] 0
let ipv42 = Symbol.make "ipv42" [] 0
let punt2 = Symbol.make "punt2" [] 0

let choice_to_double_tfxs : t list =
  [
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet2};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = ipv42; definition = Clause.id ipv42};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt2};
  ]

(* choice.p4 to early_validate.p4 *)

let choice_to_early_validate_tfxs : t list =
  [
    {defined = ethernet_validate; definition = punt_to_ethernet_validate};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4_validate; definition = punt_to_ipv4_validate};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = acl; definition = punt_to_acl};
  ]

(* choice.p4 to link_agg.p4 *)

let choice_to_link_agg_tfxs : t list =
  [
    {defined = nexthop; definition = lookup_to_nexthop};
    {defined = ethernet; definition = ethernet_lookup_to_ethernet};
    {defined = ipv4; definition = ipv4_lookup_to_ipv4};
    {defined = punt; definition = Clause.id punt};
  ]

(* double.p4 to logical.p4 *)

let double_to_logical_tfxs : t list =
  [
    {defined = punt; definition = Clause.id punt};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
  ]

(* double.p4 to action_decompose.p4 *)

let double_to_action_decompose_tfxs : t list =
  [
    {defined = ipv4_fib; definition = ipv4_to_ipv4_fib};
    {defined = ipv4_rewrite; definition = ipv4_to_ipv4_rewrite};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = punt; definition = Clause.id punt};
  ]

(* double.p4 to choice.p4 *)

let double_to_choice_tfxs : t list =
  [
    {defined = staging; definition = create_staging};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet2};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = ipv42; definition = Clause.id ipv42};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt2};
  ]

(* double.p4 to early_validate.p4 *)

let double_to_early_validate_tfxs : t list =
  [
    {defined = ethernet_validate; definition = punt_to_ethernet_validate};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4_validate; definition = punt_to_ipv4_validate};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = acl; definition = punt_to_acl};
  ]

(* double.p4 to link_agg.p4 *)

let double_to_link_agg_tfxs : t list =
  [
    {defined = nexthop; definition = lookup_to_nexthop};
    {defined = ethernet; definition = ethernet_lookup_to_ethernet};
    {defined = ipv4; definition = ipv4_lookup_to_ipv4};
    {defined = punt; definition = Clause.id punt};
  ]

(* early_validate.p4 to logical.p4 *)

let ethernet_validate = Symbol.make "ethernet_validate" [] 0
let ipv4_validate = Symbol.make "ipv4_validate" [] 0
let acl = Symbol.make "acl" [] 0

let validate_acl_to_punt : Clause.t =
  Clause.(
    Project
      [
        Var.make "hdr.ethernet.etherType" 16;
        Var.make "hdr.ipv4.isValid()" 1;
        Var.make "hdr.ipv4.version" 4;
        Var.make "hdr.ipv4.srcAddr" 32;
        Var.make "hdr.ipv4.dstAddr" 32;
        Var.make "hdr.ipv4.ttl" 8;
      ]
    <<| id ethernet_validate * id ipv4_validate * id acl
    (* TODO: Drop superfluous nested action pairs to keep only `drop` (is this even necessary?) *))

let early_validate_to_logical_tfxs : t list =
  [
    {defined = punt; definition = validate_acl_to_punt};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
  ]

(* early_validate.p4 to action_decompose.p4 *)

let ipv4_to_ipv4_fib : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "port" 9])

let ipv4_to_ipv4_rewrite : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let early_validate_to_action_decompose_tfxs : t list =
  [
    {defined = ipv4_fib; definition = ipv4_to_ipv4_fib};
    {defined = ipv4_rewrite; definition = ipv4_to_ipv4_rewrite};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = punt; definition = validate_acl_to_punt};
  ]

(* early_validate.p4 to choice.p4 *)

let early_validate_to_choice_tfxs : t list =
  [
    {defined = staging; definition = create_staging};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = ipv42; definition = Clause.id ipv4};
    {defined = punt; definition = validate_acl_to_punt};
    {defined = punt2; definition = validate_acl_to_punt};
  ]

(* early_validate.p4 to double.p4 *)

let early_validate_to_double_tfxs : t list =
  [
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = ethernet2; definition = Clause.id ethernet};
    {defined = ipv4; definition = Clause.id ipv4};
    {defined = ipv42; definition = Clause.id ipv4};
    {defined = punt; definition = validate_acl_to_punt};
    {defined = punt2; definition = validate_acl_to_punt};
  ]

(* early_validate.p4 to link_agg.p4 *)

let early_validate_to_link_agg_tfxs : t list =
  [
    {defined = nexthop; definition = lookup_to_nexthop};
    {defined = ethernet; definition = ethernet_lookup_to_ethernet};
    {defined = ipv4; definition = ipv4_lookup_to_ipv4};
    {defined = punt; definition = validate_acl_to_punt};
  ]

(* link_agg.p4 to logical.p4 *)

let nexthop = Symbol.make "nexthop" [] 0

let rename_nexthop : Clause.t =
  Clause.(
    Del (Var.make "meta.nexthop" 32)
    <<| (SetTo (Var.make "nexthop" 32, Gpl.Expr.Var (Var.make "meta.nexthop" 32))
        <<| id nexthop))

let ethernet_nexthop_to_ethernet : Clause.t =
  Clause.(id ethernet >>> rename_nexthop)

let ipv4_nexthop_to_ipv4 : Clause.t =
  Clause.(
    (id ipv4 |>> Project [Var.make "nexthop" 32] >>> rename_nexthop)
    * (id ipv4 |>> Project [Var.make "dstAddr" 48]))

let link_agg_to_logical_tfxs : t list =
  [
    {defined = punt; definition = Clause.id punt};
    {defined = ethernet; definition = ethernet_nexthop_to_ethernet};
    {defined = ipv4; definition = ipv4_nexthop_to_ipv4};
  ]

(* link_agg.p4 to action_decompose.p4 *)

let ipv4_nexthop_to_ipv4_fib : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "nexthop" 32] >>> rename_nexthop)

let ipv4_nexthop_to_ipv4_rewrite : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let link_agg_to_action_decompose_tfxs : t list =
  [
    {defined = ipv4_fib; definition = ipv4_nexthop_to_ipv4_fib};
    {defined = ipv4_rewrite; definition = ipv4_nexthop_to_ipv4_rewrite};
    {defined = ethernet; definition = ethernet_nexthop_to_ethernet};
    {defined = punt; definition = Clause.id punt};
  ]

(* link_agg.p4 to choice.p4 *)

let link_agg_to_choice_tfxs : t list =
  [
    {defined = staging; definition = create_staging};
    {defined = ethernet; definition = ethernet_nexthop_to_ethernet};
    {defined = ethernet2; definition = ethernet_nexthop_to_ethernet};
    {defined = ipv4; definition = ipv4_nexthop_to_ipv4};
    {defined = ipv42; definition = ipv4_nexthop_to_ipv4};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt};
  ]

(* link_agg.p4 to double.p4 *)

let link_agg_to_double_tfxs : t list =
  [
    {defined = ethernet; definition = ethernet_nexthop_to_ethernet};
    {defined = ethernet2; definition = ethernet_nexthop_to_ethernet};
    {defined = ipv4; definition = ipv4_nexthop_to_ipv4};
    {defined = ipv42; definition = ipv4_nexthop_to_ipv4};
    {defined = punt; definition = Clause.id punt};
    {defined = punt2; definition = Clause.id punt};
  ]

(* link_agg.p4 to early_validate.p4 *)

let link_agg_to_early_validate_tfxs : t list =
  [
    {defined = ethernet_validate; definition = punt_to_ethernet_validate};
    {defined = ethernet; definition = ethernet_nexthop_to_ethernet};
    {defined = ipv4_validate; definition = punt_to_ipv4_validate};
    {defined = ipv4; definition = ipv4_nexthop_to_ipv4};
    {defined = acl; definition = punt_to_acl};
  ]

let () =
  let output_dir = "Pipelines/retargeting" in
  (* (id, configuration, input_schema, output_schema, translation) *)
  let all_tfxs =
    [
      ("lo", "ad", action_decompose_schema, logical_to_action_decompose_tfxs);
      ("lo", "ch", choice_schema, logical_to_choice_tfxs);
      ("lo", "db", double_schema, logical_to_double_tfxs);
      ("lo", "ev", early_validate_schema, logical_to_early_validate_tfxs);
      ("lo", "la", link_agg_schema, logical_to_link_agg_tfxs);
      ("ad", "lo", logical_schema, action_decompose_to_logical_tfxs);
      ("ad", "ch", choice_schema, action_decompose_to_choice_tfxs);
      ("ad", "db", double_schema, action_decompose_to_double_tfxs);
      ( "ad",
        "ev",
        early_validate_schema,
        action_decompose_to_early_validate_tfxs );
      ("ad", "la", link_agg_schema, action_decompose_to_link_agg_tfxs);
      ("ch", "lo", logical_schema, choice_to_logical_tfxs);
      ("ch", "ad", action_decompose_schema, choice_to_action_decompose_tfxs);
      ("ch", "db", double_schema, choice_to_double_tfxs);
      ("ch", "ev", early_validate_schema, choice_to_early_validate_tfxs);
      ("ch", "la", link_agg_schema, choice_to_link_agg_tfxs);
      ("db", "lo", logical_schema, double_to_logical_tfxs);
      ("db", "ad", action_decompose_schema, double_to_action_decompose_tfxs);
      ("db", "ch", choice_schema, double_to_choice_tfxs);
      ("db", "ev", early_validate_schema, double_to_early_validate_tfxs);
      ("db", "la", link_agg_schema, double_to_link_agg_tfxs);
      ("ev", "lo", logical_schema, early_validate_to_logical_tfxs);
      ( "ev",
        "ad",
        action_decompose_schema,
        early_validate_to_action_decompose_tfxs );
      ("ev", "ch", choice_schema, early_validate_to_choice_tfxs);
      ("ev", "db", double_schema, early_validate_to_double_tfxs);
      ("ev", "la", link_agg_schema, early_validate_to_link_agg_tfxs);
      ("la", "lo", logical_schema, link_agg_to_logical_tfxs);
      ("la", "ad", action_decompose_schema, link_agg_to_action_decompose_tfxs);
      ("la", "ch", choice_schema, link_agg_to_choice_tfxs);
      ("la", "db", double_schema, link_agg_to_double_tfxs);
      ("la", "ev", early_validate_schema, link_agg_to_early_validate_tfxs);
    ]
  in
  (* Map.iteri
    ~f:(fun ~key:op ~data:cnt -> printf "$%s$ & %d \\\\\n" op cnt)
    (List.fold all_tfxs
       ~init:(Map.empty (module String))
       ~f:(fun acc (_, _, _, _, _, tfxs) ->
         List.fold tfxs ~init:acc ~f:(fun acc (_, t) ->
             Clause.count_components acc t))); *)
  let _ =
    List.foldi all_tfxs
      ~init:
        (Map.singleton
           (module String)
           "lo"
           Config.
             {
               symbols = Set.singleton (module String) "lo";
               cfg =
                 Map.of_alist_exn
                   (module String)
                   (read_csv_by_table
                      (sprintf "%s/logical_inserts_1001.csv" output_dir)
                      logical_schema);
             })
      ~f:(fun _i configs (src_id, tgt_id, output_schema, tfxs) ->
        (* printf "(%d, %d, \"%s\"),\n" (i + 1)
        (List.fold tfxs ~init:0 ~f:(fun acc (_, t) -> acc + Clause.size t))
        id; *)
        let output_file = sprintf "%s/%s_%s.csv" output_dir src_id tgt_id in
        let config = Map.find_exn configs src_id in
        printf "Input:\n%s\n"
          (config.cfg |> Map.to_alist |> List.hd_exn |> snd
         |> Fn.flip List.take 5 |> Semantics.MatchActionTable.to_string);
        let start_time = Time_ns.now () in
        let config' = transform_config tfxs config in
        let end_time = Time_ns.now () in
        printf "Output:\n%s\n"
          (config'.cfg |> Map.to_alist |> List.hd_exn |> snd
         |> Fn.flip List.take 5 |> Semantics.MatchActionTable.to_string);
        let elapsed_time_us =
          Time_ns.Span.to_ns (Time_ns.diff end_time start_time) /. 1000.0
        in
        config'.cfg
        |> Map.fold ~init:[] ~f:(fun ~key ~data acc ->
               acc @ table_to_csv_lines ~schema:(Some output_schema) key data)
        |> Out_channel.write_lines output_file;
        printf "(\"%s_%s\", %.1f),\n" src_id tgt_id elapsed_time_us;
        match Map.add configs ~key:tgt_id ~data:config' with
        | `Ok configs -> configs
        | `Duplicate -> configs)
  in
  ()
