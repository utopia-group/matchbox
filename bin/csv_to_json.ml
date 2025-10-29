[@@@warning "-21"]

(*
    Convert CSV data from Pipelines/retargeting/logical_inserts_1001.csv
    to JSON format in programs/logical_inserts_1001.json

    This reuses code from bin/utils.ml for parsing CSV and converting to internal format
*)

open Core
open Stijl
open Utils

(* let schema =
   [
     ("ipv4", ["dstAddr"], [("fwd", ["dstAddr"; "port"]); ("nop", [])]);
     ("ethernet", ["dstAddr"], [("fwd", ["port"]); ("nop", [])]);
     ( "punt",
       ["etherType"; "isValid"; "version"; "srcAddr"; "dstAddr"; "ttl"],
       [("drop", [])] );
   ] *)
let schema =
  [
    ( "acl",
      [
        "meta.is_inbound";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.proto";
        "meta.l4_sport";
        "meta.l4_dport";
      ],
      [("allow", []); ("deny", [])] );
  ]

(* Convert match value to JSON-compatible string *)
let match_to_json_string = function
  | Semantics.Match.Exact bv -> Bit.Vector.to_string bv
  | Semantics.Match.Lpm (bv, prefix_len) ->
    sprintf "%s/%d" (Bit.Vector.to_string bv) prefix_len
  | Semantics.Match.Ternary tv -> Trit.Vector.to_string tv

(* Get short field name from full path (e.g., "dstAddr" from "hdr.ipv4.dstAddr") *)
let get_short_field_name field_name =
  match String.split field_name ~on:'.' with parts -> List.last_exn parts

(* Convert a match-action entry to JSON *)
let entry_to_json (table_name : string) (entry : Semantics.MatchAction.t) :
    Yojson.Basic.t =
  (* Extract matches *)
  let matches = Semantics.MatchAction.get_matches entry in
  let match_json =
    Map.fold matches ~init:[] ~f:(fun ~key ~data acc ->
        let short_name = get_short_field_name key in
        let value_str = match_to_json_string data in
        (short_name, `String value_str) :: acc)
    |> List.rev
    |> fun pairs -> `Assoc pairs
  in

  (* Extract action *)
  let action = Semantics.MatchAction.get_action entry in
  let action_name = Semantics.MagmaAction.to_string action in
  let action_json = `List [`String action_name] in

  (* Extract action data/parameters *)
  let data = Semantics.MatchAction.get_data entry in
  let data_json =
    Map.fold data ~init:[] ~f:(fun ~key ~data acc ->
        let value_str = Bit.Vector.to_string data in
        (key, `String value_str) :: acc)
    |> List.rev
    |> fun pairs -> `Assoc pairs
  in

  (* Determine priority - higher for more specific matches *)
  let priority = if Map.is_empty matches then 0 else 100 in

  `Assoc
    [
      ("table", `String table_name);
      ("matches", match_json);
      ("action", action_json);
      ("data", data_json);
      ("priority", `Int priority);
    ]

(* Main conversion function *)
let csv_to_json (input_csv : string) (output_json : string) : unit =
  (* Read CSV and parse into tables using existing read_csv_by_table function *)
  let tables = read_csv_by_table input_csv schema in
  let open Semantics in
  let ipv4_state =
    tables |> List.hd_exn |> snd
    |> List.map ~f:(fun ma ->
           MatchAction.
             {
               ma with
               matches =
                 (match ma.action with
                 | Name "allow" ->
                   Map.update ma.matches "meta.is_inbound" ~f:(fun v ->
                       Match.not (Option.value_exn v))
                 | _ -> failwith "unreachable");
               action = MagmaAction.Name "seen";
             })
  in
  let tables = tables @ [("ipv4_state", ipv4_state)] in

  (* Convert all entries to JSON *)
  let json_entries =
    List.concat_map tables ~f:(fun (table_name, entries) ->
        List.map entries ~f:(fun entry -> entry_to_json table_name entry))
  in

  (* Write to JSON file *)
  let json = `List json_entries in
  let json_str = Yojson.Basic.pretty_to_string json in
  Out_channel.write_all output_json ~data:json_str;

  Printf.printf "Converted %d entries from %s to %s\n"
    (List.length json_entries) input_csv output_json

let () =
  let args = Sys.get_argv () in
  if Array.length args <> 3 then (
    Printf.eprintf "Usage: %s <input_csv> <output_json>\n" args.(0);
    Printf.eprintf
      "Example: %s Pipelines/retargeting/logical_inserts_1001.csv \
       programs/logical_inserts_1001.json\n"
      args.(0);
    exit 1);

  let input_csv = args.(1) in
  let output_json = args.(2) in
  csv_to_json input_csv output_json
