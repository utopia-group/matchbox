open Core
open Stijl
open BaseLogic
open Semantics

let create_exact field_name value width =
  Map.singleton
    (module String)
    field_name
    (Match.exact (Bit.Vector.of_int value ~width))

let create_lpm field_name value prefix width =
  Map.singleton
    (module String)
    field_name
    (Match.Lpm (Bit.Vector.of_int value ~width, prefix))

let create_ternary field_name value =
  Map.singleton
    (module String)
    field_name
    (Match.Ternary (Trit.Vector.of_string value))

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

(* Parse match keys of various formats *)
let parse_match_key key field_names =
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

let parse_action_params params (param_names : (string * string list) list)
    action_idx =
  let parse_param_value param_str =
    match String.split param_str ~on:'#' with
    | [value_str; width_str] ->
      Bit.Vector.of_int (Int.of_string value_str)
        ~width:(Int.of_string width_str)
    | [value_str] -> Bit.Vector.of_string value_str
    | _ -> Bit.Vector.of_int 0 ~width:32
  in
  let param_parts =
    String.split params ~on:';'
    |> List.filter ~f:(fun s -> not (String.is_empty s))
  in
  let cands =
    List.filter param_names ~f:(fun (_, data) ->
        List.length data = List.length param_parts)
  in
  let action, param_names = List.nth_exn cands action_idx in
  ( MagmaAction.make action,
    List.fold2_exn param_parts param_names
      ~init:(Map.empty (module String))
      ~f:(fun acc param_str param_name ->
        Map.set acc ~key:param_name ~data:(parse_param_value param_str)) )

let parse_csv_line line =
  let parts = String.split line ~on:',' in
  match parts with
  | ["ADD"; table_name; match_key; action_params; action_idx] ->
    Some (table_name, match_key, action_params, action_idx)
  | _ -> None

let read_csv_by_table filename
    (table_schemas : (string * string list * (string * string list) list) list)
    : (string * MatchActionTable.t) list =
  let schema_map =
    List.fold table_schemas
      ~init:(Map.empty (module String))
      ~f:(fun acc (name, fields, params) ->
        Map.set acc ~key:name ~data:(fields, params))
  in
  let create_match_action_entry (key, params, action_idx)
      (field_names, (param_names : (string * string list) list)) =
    let matches = parse_match_key key field_names in
    let action, args = parse_action_params params param_names action_idx in
    MatchAction.make TCAM matches action args
  in
  (* Group entries by table name using a Map to handle non-contiguous entries *)
  filename |> In_channel.read_lines
  |> List.filter_map ~f:parse_csv_line
  |> List.fold
       ~init:(Map.empty (module String))
       ~f:(fun acc (table, key, params, action_idx) ->
         let action_idx = Int.of_string action_idx in
         Map.update acc table ~f:(function
           | None -> [(key, params, action_idx)]
           | Some existing -> (key, params, action_idx) :: existing))
  |> Map.to_alist
  |> List.map ~f:(fun (table_name, entries) ->
         let schema =
           Map.find schema_map table_name |> Option.value ~default:([], [])
         in
         let table =
           List.map (List.rev entries) ~f:(fun (key, params, action_idx) ->
               create_match_action_entry (key, params, action_idx) schema)
         in
         (table_name, table))

let format_match_value = function
  | Semantics.Match.Exact bv -> Bit.Vector.to_string bv
  | Semantics.Match.Lpm (bv, prefix_len) ->
    sprintf "%s/%d" (Bit.Vector.to_string bv) prefix_len
  | Semantics.Match.Ternary tv -> Trit.Vector.to_string tv

let table_to_csv_lines
    ?(schema : (string * string list * (string * string list) list) list option =
      None) (table_name : string) (table : MatchActionTable.t) : string list =
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

let transform_config (tfxs : t list) (config : Config.t) : Config.t =
  List.fold tfxs ~init:config ~f:(fun acc_config stmt ->
      (* eval using acc_config if want to be able to reference tables defined earlier *)
      let config' = BaseInterpreter.eval config [stmt] in
      Config.union acc_config config')

let normalize_classbench_config (input_csv : string) (output_csv : string) :
    unit =
  let parse_ip_address_with_mask ip_str =
    match String.split ip_str ~on:'/' with
    | [ip_str; mask_str] ->
      let parse_octet s = Int.of_string s |> Int.max 0 |> Int.min 255 in
      let ip_val =
        match String.split ip_str ~on:'.' with
        | [a; b; c; d] ->
          List.fold [a; b; c; d] ~init:0 ~f:(fun acc octet ->
              (acc lsl 8) lor parse_octet octet)
        | _ -> 0
      in
      let mask_len = Int.of_string mask_str in
      (ip_val, mask_len)
    | _ -> (0, 32)
  in
  let format_match_value field_name value width =
    match value with
    | Some (ip_val, prefix_len) when String.is_suffix field_name ~suffix:"Addr"
      ->
      (* LPM *)
      sprintf "%d/%d#%d" ip_val prefix_len width
    | Some (val_int, _) ->
      (* Exact match format *)
      sprintf "%d#%d" val_int width
    | None when String.is_suffix field_name ~suffix:"Addr" ->
      (* Wildcard LPM *)
      sprintf "0/0#%d" width
    | None ->
      (* Wildcard Ternary *)
      String.make width '*'
  in
  let parse_rule_line line =
    let fields = String.split line ~on:',' |> List.map ~f:String.strip in
    let field_map =
      List.fold fields
        ~init:(Map.empty (module String))
        ~f:(fun acc field ->
          match String.split field ~on:'=' with
          | [key; value] ->
            Map.set acc ~key:(String.strip key) ~data:(String.strip value)
          | _ -> acc)
    in
    let dst_addr =
      Option.map (Map.find field_map "nw_dst") ~f:parse_ip_address_with_mask
    in
    let src_addr =
      Option.map (Map.find field_map "nw_src") ~f:parse_ip_address_with_mask
    in
    let proto =
      Option.map (Map.find field_map "nw_proto") ~f:(fun p ->
          (Int.of_string p, 0))
    in
    let sport =
      Option.map (Map.find field_map "tp_src") ~f:(fun p ->
          (Int.of_string p, 0))
    in
    let dport =
      Option.map (Map.find field_map "tp_dst") ~f:(fun p ->
          (Int.of_string p, 0))
    in
    let dst_addr_str = format_match_value "hdr.ipv4.dstAddr" dst_addr 32 in
    let src_addr_str = format_match_value "hdr.ipv4.srcAddr" src_addr 32 in
    let proto_str = format_match_value "hdr.ipv4.proto" proto 8 in
    let sport_str = format_match_value "meta.l4_sport" sport 16 in
    let dport_str = format_match_value "meta.l4_dport" dport 16 in
    sprintf "ADD,acl,%s;%s;%s;%s;%s,,0" dst_addr_str src_addr_str proto_str
      sport_str dport_str
  in
  input_csv |> In_channel.read_lines
  |> List.map ~f:parse_rule_line
  |> Out_channel.write_lines output_csv
