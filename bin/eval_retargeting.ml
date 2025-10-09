[@@@warning "-32"]

open Core
open Stijl
open BaseLogic
open Semantics

(* Parse match keys of various formats *)
let parse_match_key key field_names =
  let create_exact field_name value width =
    Map.singleton
      (module String)
      field_name
      (Match.exact (Bit.Vector.of_int value ~width))
  in
  let create_lpm field_name value prefix width =
    Map.singleton
      (module String)
      field_name
      (Match.Lpm (Bit.Vector.of_int value ~width, prefix))
  in
  let create_ternary field_name value =
    Map.singleton
      (module String)
      field_name
      (Match.Ternary (Trit.Vector.of_string value))
  in
  let parse_ip_address ip_str =
    (* Convert IP address string to integer *)
    let parse_octet s = Int.of_string s |> Int.max 0 |> Int.min 255 in
    match String.split ip_str ~on:'.' with
    | [a; b; c; d] -> (
      try
        List.fold [a; b; c; d] ~init:0 ~f:(fun acc octet ->
            (acc lsl 8) lor parse_octet octet)
      with _ -> Int.of_string_opt ip_str |> Option.value ~default:0)
    | _ -> Int.of_string_opt ip_str |> Option.value ~default:0
  in
  if String.contains key ';' then
    (* Handle multi-field entries *)
    let field_parts = String.split key ~on:';' in
    List.fold2_exn field_parts field_names
      ~init:(Map.empty (module String))
      ~f:(fun acc field field_name ->
        let match_value =
          if String.contains field '/' then
            match String.split field ~on:'#' with
            | [ip_prefix; width_str] -> (
              let width = Int.of_string width_str in
              match String.split ip_prefix ~on:'/' with
              | [ip_str; prefix_str] ->
                let value = parse_ip_address ip_str in
                let prefix_len = Int.of_string prefix_str in
                Match.Lpm (Bit.Vector.of_int value ~width, prefix_len)
              | _ -> Match.exact (Bit.Vector.of_int 0 ~width))
            | _ -> Match.exact (Bit.Vector.of_int 0 ~width:32)
          else
            match String.split field ~on:'#' with
            | [value_str; width_str] ->
              let value = try Int.of_string value_str with _ -> 0 in
              let width = Int.of_string width_str in
              Match.exact (Bit.Vector.of_int value ~width)
            | [value_str] -> (
              let trit = Trit.Vector.of_string value_str in
              try trit |> Trit.Vector.to_bv_exn |> Match.exact
              with _ -> Match.Ternary trit)
            | _ -> Match.exact (Bit.Vector.of_int 0 ~width:32)
        in
        Map.set acc ~key:field_name ~data:match_value)
  else if String.contains key '/' then
    let field_name = List.hd_exn field_names in
    match String.split key ~on:'#' with
    | [ip_prefix; width_str] -> (
      let width = Int.of_string width_str in
      match String.split ip_prefix ~on:'/' with
      | [ip_str; prefix_str] ->
        let value = parse_ip_address ip_str in
        let prefix_len = Int.of_string prefix_str in
        create_lpm field_name value prefix_len width
      | _ -> create_exact field_name 0 width)
    | [ip] -> (
      match String.split ip ~on:'/' with
      | [ip_str; prefix_str] ->
        let v = Bit.Vector.of_string ip_str in
        create_lpm field_name (Bit.Vector.to_int v) (Int.of_string prefix_str)
          (Bit.Vector.length v)
      | [ip_str] ->
        let v = Bit.Vector.of_string ip_str in
        create_exact field_name (Bit.Vector.to_int v) (Bit.Vector.length v)
      | _ -> create_exact field_name 0 32)
    | _ -> create_exact field_name 0 32
  else
    let field_name = List.hd_exn field_names in
    match String.split key ~on:'#' with
    | [value_str; width_str] ->
      let value = try Int.of_string value_str with _ -> 0 in
      let width = Int.of_string width_str in
      create_exact field_name value width
    | [ip] -> (
      match String.split ip ~on:'/' with
      | [ip_str; prefix_str] ->
        let v = Bit.Vector.of_string ip_str in
        create_lpm field_name (Bit.Vector.to_int v) (Int.of_string prefix_str)
          (Bit.Vector.length v)
      | [ip_str] -> (
        let tv = Trit.Vector.of_string ip_str in
        try
          let v = Trit.Vector.to_bv_exn tv in
          create_exact field_name (Bit.Vector.to_int v) (Bit.Vector.length v)
        with _ -> create_ternary field_name ip_str)
      | _ -> create_exact field_name 0 32)
    | _ -> create_exact field_name 0 32

let parse_action_params params param_names =
  let parse_param_value param_str =
    match String.split param_str ~on:'#' with
    | [value_str; width_str] ->
      Bit.Vector.of_int (Int.of_string value_str)
        ~width:(Int.of_string width_str)
    | [value_str] -> Bit.Vector.of_string value_str
    | _ -> Bit.Vector.of_int 0 ~width:32
  in
  if String.is_empty params || List.is_empty param_names then
    Map.empty (module String)
  else
    let param_parts =
      String.split params ~on:';'
      |> List.filter ~f:(fun s -> not (String.is_empty s))
    in
    let min_length =
      Int.min (List.length param_parts) (List.length param_names)
    in
    let params_to_use = List.take param_parts min_length in
    let names_to_use = List.take param_names min_length in
    List.fold2_exn params_to_use names_to_use ~init:String.Map.empty
      ~f:(fun acc param_str param_name ->
        Map.set acc ~key:param_name ~data:(parse_param_value param_str))

let parse_csv_line line =
  let parts = String.split line ~on:',' in
  match parts with
  | ["ADD"; table_name; match_key; action_params; _] ->
    Some (table_name, match_key, action_params)
  | _ -> None

let read_csv_by_table (filename : string)
    (table_schemas : (string * string list * string list) list) :
    (string * MatchActionTable.t) list =
  let schema_map =
    List.fold table_schemas
      ~init:(Map.empty (module String))
      ~f:(fun acc (name, fields, params) ->
        Map.set acc ~key:name ~data:(fields, params))
  in
  let create_match_action_entry (key, params) (field_names, param_names) =
    let matches = parse_match_key key field_names in
    let args = parse_action_params params param_names in
    let action = MagmaAction.make "action" in
    MatchAction.make TCAM matches action args
  in
  (* Group entries by table name using a Map to handle non-contiguous entries *)
  filename |> In_channel.read_lines
  |> List.filter_map ~f:parse_csv_line
  |> List.fold
       ~init:(Map.empty (module String))
       ~f:(fun acc (table, key, params) ->
         Map.update acc table ~f:(function
           | None -> [(key, params)]
           | Some existing -> (key, params) :: existing))
  |> Map.to_alist
  |> List.map ~f:(fun (table_name, entries) ->
         let schema =
           Map.find schema_map table_name |> Option.value ~default:([], [])
         in
         let table =
           List.map (List.rev entries) ~f:(fun (key, params) ->
               create_match_action_entry (key, params) schema)
         in
         (table_name, table))

let format_match_value = function
  | Semantics.Match.Exact bv -> Bit.Vector.to_string bv
  | Semantics.Match.Lpm (bv, prefix_len) ->
    sprintf "%s/%d" (Bit.Vector.to_string bv) prefix_len
  | Semantics.Match.Ternary tv -> Trit.Vector.to_string tv

let table_to_csv_lines
    ?(schema : (string * string list * string list) list option = None)
    (table_name : string) (table : MatchActionTable.t) : string list =
  let format_row row =
    let match_key =
      match schema with
      | Some schema_list -> (
        match
          List.find schema_list ~f:(fun (name, _, _) ->
              String.equal name table_name)
        with
        | Some (_, field_names, _) ->
          let matches = Semantics.MatchAction.get_matches row |> Map.to_alist in
          (* Sort matches by field order in schema *)
          let ordered_matches =
            List.map field_names ~f:(fun field_name ->
                List.find matches ~f:(fun (name, _) ->
                    String.equal name field_name)
                |> Option.map ~f:(fun (_, value) -> format_match_value value)
                |> Option.value ~default:"0")
          in
          String.concat ~sep:";" ordered_matches
        | None ->
          Semantics.MatchAction.get_matches row
          |> Map.to_alist
          |> List.map ~f:(fun (_, value) -> format_match_value value)
          |> String.concat ~sep:";")
      | None ->
        Semantics.MatchAction.get_matches row
        |> Map.to_alist
        |> List.map ~f:(fun (_, value) -> format_match_value value)
        |> String.concat ~sep:";"
    in
    let action_params =
      Semantics.MatchAction.get_data row
      |> Map.to_alist
      |> List.map ~f:(fun (_, bv) -> Bit.Vector.to_string bv)
      |> String.concat ~sep:";"
    in
    sprintf "ADD,%s,%s,%s,0" table_name match_key action_params
  in
  List.map table ~f:format_row

let transform_mats (tfxs : t list) (mats : (string * MatchActionTable.t) list) :
    (Symbol.t * MatchActionTable.t) list =
  let create_config mats =
    let symbols = List.map mats ~f:fst |> String.Set.of_list in
    let cfg_map =
      List.fold mats
        ~init:(Map.empty (module String))
        ~f:(fun acc (name, table) -> Map.set acc ~key:name ~data:table)
    in
    Config.{symbols; cfg = cfg_map}
  in
  let config = create_config mats in
  snd
    (List.fold tfxs ~init:(config, [])
       ~f:(fun (acc_config, acc_mats) {defined; definition} ->
         (* eval using acc_config if you want to be able to reference tables defined earlier *)
         let tmp = (defined, BaseInterpreter.eval_ definition config) in
         (Config.set acc_config (Symbol.to_string defined) (snd tmp), acc_mats @ [tmp])))

let logical_schema =
  [
    ("ipv4", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
  ]

let action_decompose_schema =
  [
    ("ipv4_fib", ["hdr.ipv4.dstAddr"], ["port"]);
    ("ipv4_rewrite", ["hdr.ipv4.dstAddr"], ["dstAddr"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
  ]

let early_validate_schema =
  [
    ( "ethernet_validate",
      ["hdr.ethernet.etherType"; "hdr.ipv4.isValid()"; "hdr.ipv4.ttl"],
      [] );
    ("ipv4_validate", ["hdr.ipv4.version"; "hdr.ipv4.ttl"], []);
    ("ipv4", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "acl",
      [
        "hdr.ethernet.srcAddr";
        "hdr.ethernet.dstAddr";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
      ],
      [] );
  ]

let choice_schema =
  [
    ("staging", ["standard_metadata.ingress_port"], ["c"]);
    ("ipv4", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ipv42", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ("ethernet2", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
    ( "punt2",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
  ]

let double_schema =
  [
    ("ipv4", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ipv42", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ("ethernet2", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
    ( "punt2",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
  ]

let link_agg_schema =
  [
    (* ("lookup", ["port"; "meta.nexthop"], ["nexthop"; "port"]); *)
    ("nexthop", ["meta.nexthop"], ["port"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["nexthop"]);
    ("ipv4", ["hdr.ipv4.dstAddr"], ["dstAddr"; "nexthop"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
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
  Clause.table
    [
      MatchAction.make TCAM
        (Map.singleton
           (module String)
           "standard_metadata.ingress_port"
           (Match.Ternary (Trit.Vector.wc 9)))
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
    ( Bit.Vector.enumerate 9
      |> List.fold
           ~init:([], Set.empty (module Int))
           ~f:(fun (mas, seen_nexthops) port ->
             let nexthop = make_unique seen_nexthops (Bit.Vector.random 32) in
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

(* Original hardcoded transformation *)
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
  (* (id, output_name, input_file, input_schema, output_schema, translation) *)
  let all_tfxs =
    [
      ( "lo_ad",
        "logical_inserts_1001.csv",
        logical_schema,
        action_decompose_schema,
        logical_to_action_decompose_tfxs );
      ( "lo_ch",
        "logical_inserts_1001.csv",
        logical_schema,
        choice_schema,
        logical_to_choice_tfxs );
      ( "lo_db",
        "logical_inserts_1001.csv",
        logical_schema,
        double_schema,
        logical_to_double_tfxs );
      ( "lo_ev",
        "logical_inserts_1001.csv",
        logical_schema,
        early_validate_schema,
        logical_to_early_validate_tfxs );
      ( "lo_la",
        "logical_inserts_1001.csv",
        logical_schema,
        link_agg_schema,
        logical_to_link_agg_tfxs );
      ( "ad_lo",
        "lo_ad.csv",
        action_decompose_schema,
        logical_schema,
        action_decompose_to_logical_tfxs );
      ( "ad_ch",
        "lo_ad.csv",
        action_decompose_schema,
        choice_schema,
        action_decompose_to_choice_tfxs );
      ( "ad_db",
        "lo_ad.csv",
        action_decompose_schema,
        double_schema,
        action_decompose_to_double_tfxs );
      ( "ad_ev",
        "lo_ad.csv",
        action_decompose_schema,
        early_validate_schema,
        action_decompose_to_early_validate_tfxs );
      ( "ad_la",
        "lo_ad.csv",
        action_decompose_schema,
        link_agg_schema,
        action_decompose_to_link_agg_tfxs );
      ( "ch_lo",
        "lo_ch.csv",
        choice_schema,
        logical_schema,
        choice_to_logical_tfxs );
      ( "ch_ad",
        "lo_ch.csv",
        choice_schema,
        action_decompose_schema,
        choice_to_action_decompose_tfxs );
      ("ch_db", "lo_ch.csv", choice_schema, double_schema, choice_to_double_tfxs);
      ( "ch_ev",
        "lo_ch.csv",
        choice_schema,
        early_validate_schema,
        choice_to_early_validate_tfxs );
      ( "ch_la",
        "lo_ch.csv",
        choice_schema,
        link_agg_schema,
        choice_to_link_agg_tfxs );
      ( "db_lo",
        "lo_db.csv",
        double_schema,
        logical_schema,
        double_to_logical_tfxs );
      ( "db_ad",
        "lo_db.csv",
        double_schema,
        action_decompose_schema,
        double_to_action_decompose_tfxs );
      ("db_ch", "lo_db.csv", double_schema, choice_schema, double_to_choice_tfxs);
      ( "db_ev",
        "lo_db.csv",
        double_schema,
        early_validate_schema,
        double_to_early_validate_tfxs );
      ( "db_la",
        "lo_db.csv",
        double_schema,
        link_agg_schema,
        double_to_link_agg_tfxs );
      ( "ev_lo",
        "lo_ev.csv",
        early_validate_schema,
        logical_schema,
        early_validate_to_logical_tfxs );
      ( "ev_ad",
        "lo_ev.csv",
        early_validate_schema,
        action_decompose_schema,
        early_validate_to_action_decompose_tfxs );
      ( "ev_ch",
        "lo_ev.csv",
        early_validate_schema,
        choice_schema,
        early_validate_to_choice_tfxs );
      ( "ev_db",
        "lo_ev.csv",
        early_validate_schema,
        double_schema,
        early_validate_to_double_tfxs );
      ( "ev_la",
        "lo_ev.csv",
        early_validate_schema,
        link_agg_schema,
        early_validate_to_link_agg_tfxs );
      ( "la_lo",
        "lo_la.csv",
        link_agg_schema,
        logical_schema,
        link_agg_to_logical_tfxs );
      ( "la_ad",
        "lo_la.csv",
        link_agg_schema,
        action_decompose_schema,
        link_agg_to_action_decompose_tfxs );
      ( "la_ch",
        "lo_la.csv",
        link_agg_schema,
        choice_schema,
        link_agg_to_choice_tfxs );
      ( "la_db",
        "lo_la.csv",
        link_agg_schema,
        double_schema,
        link_agg_to_double_tfxs );
      ( "la_ev",
        "lo_la.csv",
        link_agg_schema,
        early_validate_schema,
        link_agg_to_early_validate_tfxs );
    ]
  in
  (* Map.iteri
    ~f:(fun ~key:op ~data:cnt -> printf "$%s$ & %d \\\\\n" op cnt)
    (List.fold all_tfxs
       ~init:(Map.empty (module String))
       ~f:(fun acc (_, _, _, _, _, tfxs) ->
         List.fold tfxs ~init:acc ~f:(fun acc (_, t) ->
             Clause.count_components acc t))); *)
  List.iteri all_tfxs
    ~f:(fun _i (_id, input_file, input_schema, output_schema, tfxs) ->
      (* printf "(%d, %d, \"%s\"),\n" (i + 1)
        (List.fold tfxs ~init:0 ~f:(fun acc (_, t) -> acc + Clause.size t))
        id; *)
      let input_file = sprintf "%s/%s" output_dir input_file in
      let output_file = sprintf "%s/%s.csv" output_dir _id in
      let parsed_tables = read_csv_by_table input_file input_schema in
      let start_time = Time_ns.now () in
      let translated_tables = transform_mats tfxs parsed_tables in
      let end_time = Time_ns.now () in
      let elapsed_time_us =
        Time_ns.Span.to_ns (Time_ns.diff end_time start_time) /. 1000.0
      in
      translated_tables
      |> List.concat_map ~f:(fun (table_sym, table) ->
             table_to_csv_lines ~schema:(Some output_schema)
               table_sym.Symbol.name table)
      |> Out_channel.write_lines output_file;
      (* printf "Translating %s completed in %.1f μs\n" name elapsed_time_us) *)
      printf "(\"%s\", %.1f),\n" _id elapsed_time_us)
