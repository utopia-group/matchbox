open Core
open Stijl
open BaseLogic
open Semantics

(* Source table symbols *)
let ethernet = Symbol.make "ethernet" [] 0
let ipv4 = Symbol.make "ipv4" [] 0
let punt = Symbol.make "punt" [] 0

(* Parse match keys of various formats *)
let parse_match_key key =
  let create_exact value width =
    Map.singleton
      (module String)
      "key"
      (Match.Exact (Bit.Vector.of_int value ~width))
  in
  let create_lpm value prefix width =
    Map.singleton
      (module String)
      "key"
      (Match.Lpm (Bit.Vector.of_int value ~width, prefix))
  in
  if String.contains key '/' then
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

let parse_action_params params =
  if String.is_empty params then String.Map.empty
  else
    let param_parts = String.split params ~on:';' in
    List.foldi param_parts ~init:String.Map.empty ~f:(fun i acc part ->
        if String.is_empty part then acc
        else
          match String.split part ~on:'#' with
          | [value_str; width_str] ->
            let value = try Int.of_string value_str with _ -> 0 in
            let width = Int.of_string width_str in
            Map.set acc
              ~key:(Printf.sprintf "param%d" i)
              ~data:(Bit.Vector.of_int value ~width)
          | _ -> acc)

let parse_csv_line line =
  let parts = String.split line ~on:',' in
  match parts with
  | ["ADD"; table_name; match_key; action_params; _] ->
    Some (table_name, match_key, action_params)
  | _ -> None

let read_csv_by_table (filename : string) : (string * MatchActionTable.t) list =
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
         let table =
           List.map (List.rev entries) ~f:(fun (key, params) ->
               let matches = parse_match_key key in
               let args = parse_action_params params in
               let action = Action.make "action" args in
               MatchAction.make matches action)
         in
         (table_name, table))

let format_match_value = function
  | Semantics.Match.Exact bv -> Bit.Vector.to_string bv
  | Semantics.Match.Lpm (bv, prefix_len) ->
    Printf.sprintf "%s/%d" (Bit.Vector.to_string bv) prefix_len
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
        Semantics.MatchAction.get_action row
        |> Semantics.Action.get_data |> Map.to_alist
        |> List.map ~f:(fun (_param, bv) -> Bit.Vector.to_string bv)
        |> String.concat ~sep:";"
      in
      (* Format as ADD,<table>,<match_key>,<action_params>,0 *)
      Printf.sprintf "ADD,%s,%s,%s,0" table_name match_key action_params)

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
    (transformer :
      (string * MatchActionTable.t) list -> (string * MatchActionTable.t) list)
    (output_file : string) : unit =
  read_csv_by_table input_file
  |> transformer
  |> List.concat_map ~f:(fun (table_name, table) ->
         table_to_csv_lines table_name table)
  |> Out_channel.write_lines output_file

(* logical.p4 to action_decompose.p4 *)

let ipv4_to_fib : Clause.t = Clause.(id ipv4 |>> Project [Var.make "port" 9] )
let ipv4_to_rewrite : Clause.t = Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let action_decompose_tfxs : (string * Clause.t) list =
  [("ipv4_fib", ipv4_to_fib); ("ipv4_rewrite", ipv4_to_rewrite)]

let transform_to_action_decompose
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats action_decompose_tfxs input_tables

(* logical.p4 to choice.p4 *)

let ethernet_to_ethernet : Clause.t = Clause.id ethernet
let ethernet_to_ethernet2 : Clause.t = Clause.id ethernet
let ipv4_to_ipv4 : Clause.t = Clause.id ipv4
let ipv4_to_ipv42 : Clause.t = Clause.id ipv4
let punt_to_punt : Clause.t = Clause.id punt
let punt_to_punt2 : Clause.t = Clause.id punt

let ethernet_to_staging : Clause.t =
  Clause.table [
    Map.of_alist_exn (module String) ["c", Bit.Vector.of_int 3 ~width:4]
    |> Action.make "set_choice"
    |> MatchAction.make (Map.of_alist_exn (module String) ["standard_metadata.ingress_port", Match.Ternary (Trit.Vector.wc 9)])
  ]
  (* MapOut
    ( MapIn
        ( Id ethernet,
          MatchTfx.SetTo
            ( "standard_metadata.ingress_port",
              MatchTfx.Match (Semantics.Match.Ternary (Trit.Vector.wc 9)) ) ),
      ActionTfx.SetTo ("c", ActionTfx.Data (Bit.Vector.of_int 3 ~width:4)) ) *)

let choice_tfxs : (string * Clause.t) list =
  [
    ("staging", ethernet_to_staging);
    ("ethernet", ethernet_to_ethernet);
    ("ethernet2", ethernet_to_ethernet2);
    ("ipv4", ipv4_to_ipv4);
    ("ipv42", ipv4_to_ipv42);
    ("punt", punt_to_punt);
    ("punt2", punt_to_punt2);
  ]

let transform_to_choice (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats choice_tfxs input_tables

(* logical.p4 to double.p4 *)

(* Double tfxs use same table symbols as choice *)

let double_tfxs : (string * Clause.t) list =
  [
    ("ethernet", ethernet_to_ethernet);
    ("ethernet2", ethernet_to_ethernet2);
    ("ipv4", ipv4_to_ipv4);
    ("ipv42", ipv4_to_ipv42);
    ("punt", punt_to_punt);
    ("punt2", punt_to_punt2);
  ]

let transform_to_double (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats double_tfxs input_tables

(* logical.p4 to early_validate.p4 *)

let punt_to_ethernet_validate : Clause.t =
  Clause.(Project [
    Var.make "hdr.ethernet.etherType" 16; 
    Var.make "hdr.ipv4.isValid()" 1;
    Var.make "hdr.ipv4.ttl" 8
  ] <<| id punt)

let punt_to_ipv4_validate : Clause.t =
  let open Clause in
  Project [
    Var.make "hdr.ipv4.version" 4;
    Var.make "hdr.ipv4.ttl" 8
  ] <<| id punt

let punt_to_acl : Clause.t =
  let open Clause in 
  (WildCard (Var.make "hdr.ethernet.srcAddr" 32)
  <<| (WildCard (Var.make "hdr.ethernet.dstAddr" 32)
  <<| (Project [Var.make "hdr.ipv4.srcAddr" 32; Var.make "hdr.ipv4.dstAddr" 32]
  <<| id punt)))

let early_validate_tfxs : (string * Clause.t) list =
  [
    ("ethernet_validate", punt_to_ethernet_validate);
    ("ethernet", ethernet_to_ethernet);
    ("ipv4_validate", punt_to_ipv4_validate);
    ("ipv4", ipv4_to_ipv4);
    ("acl", punt_to_acl);
  ]

let transform_to_early_validate
    (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats early_validate_tfxs input_tables

(* logical.p4 to link_agg.p4 *)

let ethernet_to_ethernet : Clause.t = 
  Clause.(
    id ethernet
    |>> ActionTfx.SetTo (Var.make "nexthop" 32, Gpl.Expr.var (Var.make "param0" 9))
  )

let ipv4_to_ipv4 : Clause.t = 
  Clause.(
    id ipv4
    |>> ActionTfx.SetTo (Var.make "nexthop" 32, Gpl.Expr.var (Var.make "param1" 9))
  )

(* Create nexthop table with static mappings for ports 1-500 *)
let create_nexthop : Clause.t =
  Clause.table (List.init 500 ~f:(fun i ->
    let port = i + 1 in
    Map.of_alist_exn (module String) ["port", Bit.Vector.of_int port ~width:9]
    |> Action.make "set_port"
    |> MatchAction.make (Map.of_alist_exn (module String) ["nexthop", Match.Exact (Bit.Vector.of_int port ~width:32)])
  ))

let punt_to_punt_linkagg : Clause.t = Clause.id punt

let link_agg_tfxs : (string * Clause.t) list =
  [
    ("ethernet", ethernet_to_ethernet);
    ("ipv4", ipv4_to_ipv4);
    ("nexthop", create_nexthop);
    ("punt", punt_to_punt_linkagg);
  ]

let transform_to_link_agg (input_tables : (string * MatchActionTable.t) list) :
    (string * MatchActionTable.t) list =
  transform_mats link_agg_tfxs input_tables

let () =
  let input_file = "Pipelines/retargeting/logical_inserts_1001.csv" in
  let output_dir = "Pipelines/retargeting" in

  let tfxs =
    [
      ("action_decompose", transform_to_action_decompose);
      ("choice", transform_to_choice);
      ("double", transform_to_double);
      ("early_validate", transform_to_early_validate);
      ("link_agg", transform_to_link_agg);
    ]
  in

  List.iter tfxs ~f:(fun (name, transform) ->
      let output_file = sprintf "%s/%s_1001.csv" output_dir name in
      transform_csv_file input_file transform output_file)
