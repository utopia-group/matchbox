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
    let symbols = List.map mats ~f:(fun (name, _) -> Symbol.make name [] 0) in
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
         let tmp = (defined, BaseInterpreter.eval definition config) in
         (Config.set acc_config defined (snd tmp), acc_mats @ [tmp])))
