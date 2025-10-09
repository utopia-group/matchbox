open Core
open Yojson
open Semantics

module Insertion = struct
  type t = { table : string;
             matches : (string * string) list;
             action : string list;
             data : (string * string) list;
             priority : int;
  } [@@deriving yojson]

  let lookup alist x = 
    List.find_map alist ~f:(fun (k, v) ->
      if String.(x = k) then 
        Some v
      else 
        None
    )

  let lookup_exn alist x = 
    let message () = Printf.sprintf "couldn't find %s in alist" x in
    lookup alist x 
    |> Option.value_exn ~message:(message ())

  let (%!) = lookup
  let (%!!) = lookup_exn


  let convert_table (schema : Type.ctx) : Safe.t -> string * Type.table = function
    | `String name -> 
      let table_typ = Type.find_table_exn schema name in 
      name, table_typ
    | json -> failwithf "failed to get table name from %s" (Safe.to_string json) ()

  let extract_match hw = function 
    | `String s ->  
      let mtch = Match.of_string s in 
      assert (Match.ensure_hw_compat mtch hw);
      mtch
    | json -> failwithf "failed to get match from %s" (Safe.to_string json) ()


  let convert_match (ttype : Type.table) : Yojson.Safe.t -> MatchExpression.t = function 
    | `Assoc matches -> 
      List.fold matches ~init:MatchExpression.empty ~f:(fun mexpr (k, v) -> 
          extract_match ttype.hw v
          |> MatchExpression.set mexpr k
        )
    | json -> failwithf "expected match to be an assoclist, got %s" (Safe.to_string json) ()

  let rec construct_action : Safe.t list -> MagmaAction.t = function 
    | [] -> failwith "all rows must have at least one action"
    | [`String name] -> 
      MagmaAction.make name
    | [`List l1; `List l2] -> 
      MagmaAction.(construct_action l1 @ construct_action l2)
    | json -> failwithf "expected action to be a binary nested list, got %s" (List.to_string ~f:Safe.to_string json) ()

  let convert_action (aset : Type.ActionSet.t) : Safe.t -> MagmaAction.t = function 
  | `List act -> 
    let act = construct_action act in 
    if Set.mem aset act then 
      act
    else 
      failwithf "coulnd't find action %s" (MagmaAction.to_string act) ()  
  | json -> failwithf "expected action to be a toplevel list, got %s" (Safe.to_string json) ()

  let convert_datum width = function
    | `String bv_str -> 
      let bv = Bit.Vector.of_string bv_str in 
      assert (width = Bit.Vector.length bv);
      bv
    | `Int bv_int -> 
      Bit.Vector.of_int bv_int ~width
    | json -> failwithf "expected data to be a string or an int list, got %s" (Safe.to_string json) ()


  let convert_data (dtype : int String.Map.t) : Safe.t -> Data.t = function
    | `Assoc ds ->
      List.fold ds ~init:Semantics.Data.empty ~f:(fun data (k,v) -> 
        let width = Map.find_exn dtype k in 
        let bv = convert_datum width v in
        Data.update data k bv
      )
    | json -> failwithf "expected action to be a toplevel assoc, got %s" (Safe.to_string json) ()

  let convert_prio = function 
  | `Int p -> p
  | json -> 
    failwithf "Priority must be an int, got %s" (Safe.to_string json) ()

  let convert_row schema (json : Yojson.Safe.t) : string * MatchAction.t * int =
    match json with 
    | `Assoc dict ->
      let table, ttyp = dict %!! "table" |> convert_table schema in
      let matches = dict %!! "matches" |> convert_match ttyp in 
      let action = dict %!! "action" |> convert_action ttyp.actions in
      let data = dict %!! "data" |> convert_data ttyp.data in
      let priority = dict %!! "priority" |> convert_prio in
      table, MatchAction.make ttyp.hw matches action data, priority
    | _ -> 
      failwith "unrecognized json"

end

let convert_trace schema (json : Yojson.Safe.t) : BaseLogic.Config.t =
  let open BaseLogic in 
  match json with 
  | `List raw_rows ->
    let rows = List.map raw_rows ~f:(Insertion.convert_row schema) in
    Type.get_tables schema
    |> List.fold ~init:Config.empty ~f:(fun config table ->
      let rows = List.filter rows ~f:(fun (tbl, _, _) -> String.(table = tbl)) in
      let sorted_rows = List.sort rows ~compare:(fun (_, _,p1) (_,_,p2) -> Int.compare p1 p2) in
      let mat = List.map sorted_rows ~f:(fun (_, row, _) -> row) in
      Config.set config table mat    
    )
  | _ -> failwithf "expected trace to be a toplevel list, got %s" (Safe.to_string json) ()

let parse_trace_file schema filename : BaseLogic.Config.t = 
  Safe.from_file filename
  |> convert_trace schema