open Core
open Stijl
open BaseLogic
open Semantics

(* Parse match keys of various formats *)
let parse_match_key key field_names =
  let create_exact value width =
    Map.singleton
      (module String)
      (List.hd_exn field_names)
      (Match.Exact (Bit.Vector.of_int value ~width))
  in
  let create_lpm value prefix width =
    Map.singleton
      (module String)
      (List.hd_exn field_names)
      (Match.Lpm (Bit.Vector.of_int value ~width, prefix))
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
                let value = try Int.of_string ip_str with _ -> 0 in
                let prefix_len = Int.of_string prefix_str in
                Match.Lpm (Bit.Vector.of_int value ~width, prefix_len)
              | _ -> Match.Exact (Bit.Vector.of_int 0 ~width))
            | _ -> Match.Exact (Bit.Vector.of_int 0 ~width:32)
          else
            match String.split field ~on:'#' with
            | [value_str; width_str] ->
              let value = try Int.of_string value_str with _ -> 0 in
              let width = Int.of_string width_str in
              Match.Exact (Bit.Vector.of_int value ~width)
            | _ -> Match.Exact (Bit.Vector.of_int 0 ~width:32)
        in
        Map.set acc ~key:field_name ~data:match_value)
  else if String.contains key '/' then
    (* Handle single field entries *)
    match String.split key ~on:'#' with
    | [ip_prefix; width_str] -> (
      let width = Int.of_string width_str in
      match String.split ip_prefix ~on:'/' with
      | [ip_str; prefix_str] ->
        let value = try Int.of_string ip_str with _ -> 0 in
        let prefix_len = Int.of_string prefix_str in
        create_lpm value prefix_len width
      | _ -> create_exact 0 width)
    | _ -> create_exact 0 32
  else
    match String.split key ~on:'#' with
    | [value_str; width_str] ->
      let value = try Int.of_string value_str with _ -> 0 in
      let width = Int.of_string width_str in
      create_exact value width
    | _ -> create_exact 0 32

let parse_action_params params param_names =
  if String.is_empty params then String.Map.empty
  else
    let param_parts = String.split params ~on:';' in
    (* Filter out empty parts to match the expected parameter count *)
    let non_empty_parts =
      List.filter param_parts ~f:(fun s -> not (String.is_empty s))
    in
    if List.is_empty non_empty_parts then String.Map.empty
    else if List.is_empty param_names then
      (* If no parameters are expected, ignore any parameters in the CSV *)
      String.Map.empty
    else
      (* Take only as many parameters as available *)
      let min_length =
        min (List.length non_empty_parts) (List.length param_names)
      in
      let params_to_use = List.take non_empty_parts min_length in
      let names_to_use = List.take param_names min_length in
      List.fold2_exn params_to_use names_to_use ~init:String.Map.empty
        ~f:(fun acc part param_name ->
          match String.split part ~on:'#' with
          | [value_str; width_str] ->
            let value = try Int.of_string value_str with _ -> 0 in
            let width = Int.of_string width_str in
            Map.set acc ~key:param_name ~data:(Bit.Vector.of_int value ~width)
          | [value_str] ->
            let value = Option.value ~default:0 (Int.of_string_opt value_str) in
            let width = if String.equal param_name "c" then 4 else 32 in
            Map.set acc ~key:param_name ~data:(Bit.Vector.of_int value ~width)
          | _ -> acc)

let parse_csv_line line =
  let parts = String.split line ~on:',' in
  match parts with
  | ["ADD"; table_name; match_key; action_params; _] ->
    Some (table_name, match_key, action_params)
  | _ -> None

let read_csv_by_table (filename : string)
    (table_schemas : (string * string list * string list) list) :
    (string * MatchActionTable.t) list =
  let lines = In_channel.read_lines filename in
  let entries = List.filter_map lines ~f:parse_csv_line in
  (* Group by table name *)
  let grouped =
    List.fold entries
      ~init:(Map.empty (module String))
      ~f:(fun acc (table, key, params) ->
        Map.update acc table ~f:(function
          | None -> [(key, params)]
          | Some existing -> (key, params) :: existing))
  in
  Map.to_alist grouped
  |> List.map ~f:(fun (table_name, entries) ->
         let field_names, param_names =
           match
             List.find table_schemas ~f:(fun (name, _, _) ->
                 String.equal name table_name)
           with
           | Some (_, fields, params) -> (fields, params)
           | None ->
             (* fallback to empty lists *)
             ([], [])
         in
         let table =
           List.map (List.rev entries) ~f:(fun (key, params) ->
               let matches = parse_match_key key field_names in
               let args = parse_action_params params param_names in
               let action = MagmaAction.make "action" in
               MatchAction.make TCAM matches action args)
         in
         (table_name, table))

let format_match_value = function
  | Semantics.Match.Exact bv -> Bit.Vector.to_string bv
  | Semantics.Match.Lpm (bv, prefix_len) ->
    sprintf "%s/%d" (Bit.Vector.to_string bv) prefix_len
  | Semantics.Match.Ternary tv -> Trit.Vector.to_string tv

let table_to_csv_lines (table_name : string) (table : MatchActionTable.t) :
    string list =
  List.map table ~f:(fun row ->
      let match_key =
        Semantics.MatchAction.get_matches row
        |> Map.to_alist
        |> List.map ~f:(fun (_field, value) -> format_match_value value)
        |> String.concat ~sep:";"
      in
      let action_params =
        Semantics.MatchAction.get_data row
        |> Map.to_alist
        |> List.map ~f:(fun (_param, bv) -> Bit.Vector.to_string bv)
        |> String.concat ~sep:";"
      in
      (* Format as ADD,<table>,<match_key>,<action_params>,0 *)
      sprintf "ADD,%s,%s,%s,0" table_name match_key action_params)

let transform_mats (tfxs : (string * Clause.t) list)
    (mats : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  (* Create config from input tables *)
  let symbols = List.map mats ~f:(fun (name, _) -> Symbol.make name [] 0) in
  let cfg_map =
    List.fold2_exn
      (List.map symbols ~f:(fun s -> s.name))
      (List.map mats ~f:snd)
      ~init:(Map.empty (module String))
      ~f:(fun acc name table -> Map.set acc ~key:name ~data:table)
  in
  let config = Config.{symbols; cfg = cfg_map} in
  List.map tfxs ~f:(fun (output_name, clause) ->
      (output_name, BaseInterpreter.eval clause config))

let transform_csv_file (input_file : string)
    (input_schema : (string * string list * string list) list)
    (transformer :
      (string * MatchActionTable.t) list -> (string * MatchActionTable.t) list)
    (output_file : string) : unit =
  read_csv_by_table input_file input_schema
  |> transformer
  |> List.concat_map ~f:(fun (table_name, table) ->
         table_to_csv_lines table_name table)
  |> Out_channel.write_lines output_file

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

let _choice_schema =
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

let _double_schema =
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

let _link_agg_schema =
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
    ("nexthop", ["hdr.ipv4.dstAddr"], ["nhop_idx"]);
  ]

let ethernet = Symbol.make "ethernet" [] 0
let ipv4 = Symbol.make "ipv4" [] 0
let punt = Symbol.make "punt" [] 0

(* logical.p4 to action_decompose.p4 *)

let ipv4_to_ipv4_fib : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "port" 9])

let ipv4_to_ipv4_rewrite : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let logical_to_action_decompose_tfxs : (string * Clause.t) list =
  [
    ("ipv4_fib", ipv4_to_ipv4_fib);
    ("ipv4_rewrite", ipv4_to_ipv4_rewrite);
    ("ethernet", Clause.id ethernet);
    ("punt", Clause.id punt);
  ]

let transform_logical_to_action_decompose
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats logical_to_action_decompose_tfxs input_tables

(* logical.p4 to choice.p4 *)

let ethernet_to_staging : Clause.t =
  let matchexpr =
    String.Map.of_alist_exn
      [("standard_metadata.ingress_port", Match.Ternary (Trit.Vector.wc 9))]
  in
  let data = String.Map.of_alist_exn [("c", Bit.Vector.of_int 3 ~width:4)] in
  let row =
    MatchAction.make TCAM matchexpr (MagmaAction.make "set_choice") data
  in
  Clause.table [row]

let logical_to_choice_tfxs : (string * Clause.t) list =
  [
    ("staging", ethernet_to_staging);
    ("ethernet", Clause.id ethernet);
    ("ethernet2", Clause.id ethernet);
    ("ipv4", Clause.id ipv4);
    ("ipv42", Clause.id ipv4);
    ("punt", Clause.id punt);
    ("punt2", Clause.id punt);
  ]

let transform_logical_to_choice
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats logical_to_choice_tfxs input_tables

(* logical.p4 to double.p4 *)

let logical_to_double_tfxs : (string * Clause.t) list =
  [
    ("ethernet", Clause.id ethernet);
    ("ethernet2", Clause.id ethernet);
    ("ipv4", Clause.id ipv4);
    ("ipv42", Clause.id ipv4);
    ("punt", Clause.id punt);
    ("punt2", Clause.id punt);
  ]

let transform_logical_to_double
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats logical_to_double_tfxs input_tables

(* logical.p4 to early_validate.p4 *)

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

let logical_to_early_validate_tfxs : (string * Clause.t) list =
  [
    ("ethernet_validate", punt_to_ethernet_validate);
    ("ethernet", Clause.id ethernet);
    ("ipv4_validate", punt_to_ipv4_validate);
    ("ipv4", Clause.id ipv4);
    ("acl", punt_to_acl);
  ]

let transform_logical_to_early_validate
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats logical_to_early_validate_tfxs input_tables

(* logical.p4 to link_agg.p4 *)

let ethernet_to_ethernet : Clause.t =
  Clause.(
    id ethernet
    |>> SetTo (Var.make "nexthop" 32, Gpl.Expr.var (Var.make "port" 9)))

let ipv4_to_ipv4 : Clause.t =
  Clause.(
    id ipv4 |>> SetTo (Var.make "nexthop" 32, Gpl.Expr.var (Var.make "port" 9)))

(* Create nexthop table with static mappings for ports 1-500 *)
let create_nexthop : Clause.t =
  Clause.table
    (MatchActionTable.of_domain (List.range 1 501) ~hw:TCAM
       ~matches:(fun port ->
         [("nexthop", Match.Exact (Bit.Vector.of_int ~width:32 port))])
       ~action:(fun _ -> "set_port")
       ~data:(fun port -> [("port", Bit.Vector.of_int ~width:9 port)]))

let link_agg_tfxs : (string * Clause.t) list =
  [
    ("ethernet", ethernet_to_ethernet);
    ("ipv4", ipv4_to_ipv4);
    ("nexthop", create_nexthop);
    ("punt", Clause.id punt);
  ]

let transform_to_link_agg (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats link_agg_tfxs input_tables

(* action_decompose.p4 to early_validate.p4 *)

let ipv4_fib = Symbol.make "ipv4_fib" [] 0
let ipv4_rewrite = Symbol.make "ipv4_rewrite" [] 0

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

let ipv4_fib_rewrite_to_ipv4 : Clause.t =
  Clause.(
    id ipv4_fib * id ipv4_rewrite
    |>> Rename
          ( MagmaAction.(make "ipv4_forward" @ make "rewrite"),
            MagmaAction.make "ipv4_forward" ))

let punt_to_acl : Clause.t =
  Clause.(
    WildCard (Var.make "hdr.ethernet.srcAddr" 32)
    <<| (WildCard (Var.make "hdr.ethernet.dstAddr" 32)
        <<| (Project
               [Var.make "hdr.ipv4.srcAddr" 32; Var.make "hdr.ipv4.dstAddr" 32]
            <<| id punt)))

let action_decompose_to_early_validate_tfxs : (string * Clause.t) list =
  [
    ("ethernet_validate", punt_to_ethernet_validate);
    ("ipv4_validate", punt_to_ipv4_validate);
    ("ipv4", ipv4_fib_rewrite_to_ipv4);
    ("ethernet", Clause.id ethernet);
    ("acl", punt_to_acl);
  ]

let transform_action_decompose_to_early_validate
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats action_decompose_to_early_validate_tfxs input_tables

(* early_validate.p4 to action_decompose.p4 *)

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
    (* TODO: Drop superfluous nested action pairs to keep only `drop` *))

let ipv4_to_ipv4_fib : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "port" 9])

let ipv4_to_ipv4_rewrite : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let early_validate_to_action_decompose_tfxs : (string * Clause.t) list =
  [
    ("ipv4_fib", ipv4_to_ipv4_fib);
    ("ipv4_rewrite", ipv4_to_ipv4_rewrite);
    ("ethernet", Clause.id ethernet);
    ("punt", validate_acl_to_punt);
  ]

let transform_early_validate_to_action_decompose
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats early_validate_to_action_decompose_tfxs input_tables

let () =
  let output_dir = "Pipelines/retargeting" in

  (* (output_name, input_file, input_schema, translation) *)
  let tfxs =
    [
      ( "logical_to_action_decompose",
        "logical_inserts_1001.csv",
        logical_schema,
        transform_logical_to_action_decompose );
      ( "logical_to_choice",
        "logical_inserts_1001.csv",
        logical_schema,
        transform_logical_to_choice );
      ( "logical_to_double",
        "logical_inserts_1001.csv",
        logical_schema,
        transform_logical_to_double );
      ( "logical_to_early_validate",
        "logical_inserts_1001.csv",
        logical_schema,
        transform_logical_to_early_validate );
      ( "logical_to_link_agg",
        "logical_inserts_1001.csv",
        logical_schema,
        transform_to_link_agg );
      ( "action_decompose_to_early_validate",
        "logical_to_action_decompose_1001.csv",
        action_decompose_schema,
        transform_action_decompose_to_early_validate );
      ( "early_validate_to_action_decompose",
        "logical_to_early_validate_1001.csv",
        early_validate_schema,
        transform_early_validate_to_action_decompose );
    ]
  in

  List.iter tfxs ~f:(fun (name, input_file, input_schema, transform) ->
      let input_file = sprintf "%s/%s" output_dir input_file in
      let output_file = sprintf "%s/%s_1001.csv" output_dir name in
      transform_csv_file input_file input_schema transform output_file)
