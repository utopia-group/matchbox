open Core

exception ParseError of string

(* OpenFlow field types *)
type openflow_field =
  | InPort of int
  | DlSrc of string
  | DlDst of string
  | DlType of int
  | EthType of int
  | NwSrc of string * int
  | NwDst of string * int
  | NwProto of int
  | TpSrc of int
  | TpDst of int

let parse_hex_value s =
  let s = String.strip s in
  let hex_str =
    if String.is_prefix ~prefix:"0x" s then String.drop_prefix s 2
    else if String.contains s ':' then
      (* Handle colon-separated MAC addresses *)
      String.split s ~on:':' |> String.concat
    else s
  in
  match Int.of_string (sprintf "0x%s" hex_str) with
  | n -> n
  | exception _ -> raise (ParseError (sprintf "Invalid hex value: %s" s))

let parse_cidr_value s =
  let s = String.strip s in
  match String.split ~on:'/' s with
  | [ip; prefix] ->
    let prefix_len =
      match Int.of_string prefix with
      | n -> n
      | exception _ ->
        raise (ParseError (sprintf "Invalid CIDR prefix: %s" prefix))
    in
    (ip, prefix_len)
  | [ip] -> (ip, 32) (* Default to /32 if no prefix specified *)
  | _ -> raise (ParseError (sprintf "Invalid CIDR format: %s" s))

let parse_field_pair pair =
  match String.split ~on:'=' pair with
  | [key; value] -> (
    let key = String.strip key in
    let value = String.strip value in
    match key with
    | "in_port" -> (
      match String.lowercase value with
      | "random" -> InPort 0 (* Treat random as port 0 *)
      | _ -> (
        match Int.of_string value with
        | n -> InPort n
        | exception _ ->
          raise (ParseError (sprintf "Invalid in_port value: %s" value))))
    | "dl_src" -> DlSrc value
    | "dl_dst" -> DlDst value
    | "eth_type" -> EthType (parse_hex_value value)
    | "nw_src" ->
      let ip, prefix = parse_cidr_value value in
      NwSrc (ip, prefix)
    | "nw_dst" ->
      let ip, prefix = parse_cidr_value value in
      NwDst (ip, prefix)
    | "nw_proto" -> (
      match Int.of_string value with
      | n -> NwProto n
      | exception _ ->
        raise (ParseError (sprintf "Invalid nw_proto value: %s" value)))
    | "tp_src" -> (
      match Int.of_string value with
      | n -> TpSrc n
      | exception _ ->
        raise (ParseError (sprintf "Invalid tp_src value: %s" value)))
    | "tp_dst" -> (
      match Int.of_string value with
      | n -> TpDst n
      | exception _ ->
        raise (ParseError (sprintf "Invalid tp_dst value: %s" value)))
    | "dl_type" -> (
      match parse_hex_value value with
      | n -> DlType n
      | exception _ ->
        raise (ParseError (sprintf "Invalid dl_type value: %s" value)))
    | _ -> raise (ParseError (sprintf "Unknown field: %s" key)))
  | _ -> raise (ParseError (sprintf "Invalid field format: %s" pair))

(* Convert OpenFlow fields to Match.t list *)
let fields_to_matches fields =
  let matches = ref (Map.empty (module String)) in
  let add_match name width value =
    let match_val = Semantics.Match.Exact (Bit.Vector.of_int ~width value) in
    matches := Map.set !matches ~key:name ~data:match_val
  in
  let add_lpm_match name width ip prefix_len =
    (* Simple IP parsing *)
    let ip_parts = String.split ~on:'.' ip in
    let ip_int =
      List.fold ip_parts ~init:0 ~f:(fun acc part ->
          match Int.of_string part with
          | n -> (acc lsl 8) lor n
          | exception _ -> raise (ParseError (sprintf "Invalid IP: %s" ip)))
    in
    let match_val =
      Semantics.Match.Lpm (Bit.Vector.of_int ~width ip_int, prefix_len)
    in
    matches := Map.set !matches ~key:name ~data:match_val
  in
  List.iter fields ~f:(function
    | InPort port -> add_match "in_port" 16 port
    | DlSrc mac ->
      let mac_int = parse_hex_value mac in
      add_match "dl_src" 48 mac_int
    | DlDst mac ->
      let mac_int = parse_hex_value mac in
      add_match "dl_dst" 48 mac_int
    | DlType dl_type -> add_match "dl_type" 16 dl_type
    | EthType eth_type -> add_match "eth_type" 16 eth_type
    | NwSrc (ip, prefix) -> add_lpm_match "nw_src" 32 ip prefix
    | NwDst (ip, prefix) -> add_lpm_match "nw_dst" 32 ip prefix
    | NwProto proto -> add_match "nw_proto" 8 proto
    | TpSrc port -> add_match "tp_src" 16 port
    | TpDst port -> add_match "tp_dst" 16 port);
  !matches

let parse_rule_line line =
  let line = String.strip line in
  if String.is_empty line then raise (ParseError "Empty rule line")
  else
    let pairs = String.split ~on:',' line in
    let fields = List.map pairs ~f:parse_field_pair in
    let matches = fields_to_matches fields in
    let action = Semantics.MagmaAction.make "forward" in
    let data = String.Map.empty in
    (* Default action *)
    Semantics.MatchAction.{hw = TCAM; matches; action; data}

(* Parse multiple rules from a string *)
let parse_from_string content =
  let lines = String.split_lines content in
  let non_empty_lines =
    List.filter lines ~f:(fun line -> not (String.is_empty (String.strip line)))
  in
  List.map non_empty_lines ~f:parse_rule_line

let parse_from_file filename =
  match In_channel.read_all filename with
  | content -> parse_from_string content
  | exception exn ->
    raise
      (ParseError
         (sprintf "Failed to read file %s: %s" filename (Exn.to_string exn)))
