open Core

module Var = Gpl.Var

module Symbol = struct
  type t = {name : string; ins : int list; out : int} [@@deriving sexp, compare]
  let make name ins out = {name; ins; out}
  let (=) f g = String.(f.name = g.name)

  let to_string symbol = symbol.name

end

module Loc = struct 
  type t = (Symbol.t * int) 

  let (=) ((s,i) : t) ((s',i') : t) = 
    Symbol.(s = s') && Int.(i = i')

  let to_string (s,i) = Printf.sprintf "%s@%d" (Symbol.to_string s) i

end

module Provenance = struct
  type t = Loc.t list option

  let (let+) o f = Option.map o ~f
  let (let*) o f = Option.bind o ~f

  let (=) : t -> t -> bool = Option.equal (List.equal Loc.(=))

  let remove (prov : t) locs_to_delete : t = 
    let+ locs = prov in 
    List.filter locs ~f:(fun loc ->
        not (List.mem locs_to_delete loc ~equal:Loc.(=))
    )

  let add loc prov = 
    match prov with 
    | None -> failwith "adding provenance to given" 
    | Some locs -> 
      if List.mem locs loc ~equal:Loc.(=) then 
        Some locs 
      else 
        Some (loc::locs)

  let union (prov1 : t) (prov2 : t) = 
    let* xs = prov1 in 
    let+ ys = prov2 in
    List.rev xs
    |> List.fold ~init:ys ~f:(fun union x -> 
      if List.mem union x ~equal:Loc.(=) then 
        union 
      else 
        x :: union 
    )
  
  let consistent_partition above below ~equal =
    List.for_all above ~f:(fun loc_above -> 
      List.for_all below ~f:(equal loc_above))

  let is_empty (p : t) = 
    match p with 
    | Some [] -> true 
    | _ -> true

  let is_given = Option.is_none

end

module ProvRow = struct
  type t = {
    loc : Loc.t;
    row : Semantics.MatchAction.t;
    prov : Provenance.t
  }

  let equal prow1 prow2 =
    if Loc.(prow1.loc = prow2.loc) then begin
      assert (Semantics.MatchAction.equal prow1.row prow2.row);
      assert (Provenance.(prow1.prov = prow2.prov));
      true
    end else
      false

  let add (r : t) table idx : t = 
    { r with 
      prov = Provenance.add (table, idx) r.prov
    }

  let does_match data provrow = 
    Semantics.MatchAction.does_match data provrow.row

  let pivot listmap : 'a String.Map.t list =
    Map.fold listmap ~init:[String.Map.empty] ~f:(fun ~key ~data maps -> 
      List.bind data ~f:(fun datum -> 
        List.map maps ~f:(fun map -> 
          Map.add_exn map ~key ~data:datum)
      )
    )

  let op (r : t) : t list = 
    let open Semantics in 
    let m = MatchAction.get_matches r.row in 
    let a = MatchAction.get_action r.row in 
    let aid = Action.get_name a in 
    let dat = Action.get_data a in 
    let m' = String.Map.map dat ~f:(Match.exact) in 
    let mk_act args = Action.make aid args in 
    let mk_provrow args = 
      {r with row = MatchAction.make m' (mk_act args)}
    in 
    let args' = String.Map.map m ~f:Match.unsafe_explicit_set in 
    let args'' = pivot args' in
    List.map args'' ~f:mk_provrow

end

module IdGen : sig 
  type t 
  val init : unit -> t
  val fresh : t -> int * t
end = struct
  type t = int
  let init () : t = 0
  let fresh i : int * t = (i, i + 1)
end

module ProvTable = struct
  type t = 
    { name : string; 
      ins  : int list;
      out : int;
      idgen : IdGen.t;
      rows : ProvRow.t list }
  
  let symbol ({name;ins;out;_} : t) : Symbol.t =
    {name;ins;out}

  let insert ~into:tbl ~after:idx row prov =
    let id, idgen = IdGen.fresh tbl.idgen in 
    let loc = symbol tbl, id in 
    let provrow = ProvRow.{loc;row;prov} in
    let above, below = 
      List.split_n tbl.rows idx
    in 
    let rows = above @ [provrow] @ below in 
    { tbl with idgen; rows }

  let remove_if_exists ~from:tbl loc =
    {tbl with 
      rows = List.filter tbl.rows ~f:(fun r -> Loc.(r.loc = loc))
    }

  let remove_exn ~from:tbl loc =
    let exists =
      List.exists tbl.rows ~f:(fun r -> Loc.(r.loc = loc))
    in
    if exists then 
      remove_if_exists ~from:tbl loc
    else
      failwithf "RemoveError: Could not find %s in table %s" (Loc.to_string loc) (tbl.name) ()
   
  let image table data = 
    List.filter_map table.rows ~f:(fun row -> 
      if ProvRow.does_match data row then 
        Some (row.row.action)
      else 
        None
    )

  let preimage_rows table (output_row : Semantics.MatchAction.t) = 
    List.filter table.rows ~f:(fun provrow -> 
      Semantics.MatchAction.does_match provrow.row.action.args output_row)

  let matching_rows table data =
    List.filter table.rows ~f:(ProvRow.does_match data)

end

module Config = struct 
  type t = {
    symbols : Symbol.t list;
    cfg : ProvTable.t String.Map.t;
  }

  let _find_raw_exn cfg x = Map.find_exn cfg.cfg x

  let find_exn cfg (symbol : Symbol.t) : ProvTable.t =
    _find_raw_exn cfg symbol.name

  let set config (symbol : Symbol.t) table = 
    let add_if_not_exists f gs = 
      if List.mem gs f ~equal:Symbol.(=) then
        gs
      else
        f::gs
    in
    {
      symbols = add_if_not_exists symbol config.symbols;
      cfg = Map.set config.cfg ~key:symbol.name ~data:table;
    }
  let get_tables config = config.symbols

  let get_index config (loc : Loc.t) : Symbol.t * int = 
    let tblname,_ = loc in
    let table = find_exn config tblname in 
    let i, _ = List.findi_exn table.rows ~f:(fun _ row -> 
      Loc.(loc = row.loc)
    ) in
    tblname, i

  let rec remove config locs = 
    let cfg = String.Map.map config.cfg ~f:(fun provtable -> 
      let rows = List.filter_map provtable.rows ~f:(fun provrow -> 
        if List.mem locs provrow.loc ~equal:Loc.(=) then
          None
        else
          Some {provrow with 
            prov = Provenance.remove provrow.prov locs
          }
      ) in
      {provtable with rows}
    ) in
    let empty_locs = 
      Map.fold cfg ~init:[] ~f:(fun ~key:_ ~data:provtable acc -> 
        acc @ 
        List.filter_map provtable.rows ~f:(fun provrow -> 
          if Provenance.is_empty provrow.prov then 
            Some provrow.loc
          else
            None
        )
      )
    in
    if List.is_empty empty_locs then 
      {config with cfg}
    else
      remove config empty_locs

end


module MatchTfx = struct
  type expr = 
    | Var of string 
    | Match of Semantics.Match.t
    | AddK of expr * Bit.Vector.t
    | SubK of expr * Bit.Vector.t
  [@@deriving sexp, compare]

  type t = 
    | Project of string list
    | SetTo of string * expr
  [@@deriving sexp, compare]
end

module ActionTfx = struct
  type expr = 
    | Var of string 
    | Data of Bit.Vector.t
    | AddK of expr * Bit.Vector.t
    | SubK of expr * Bit.Vector.t
  [@@deriving sexp, compare]

  type t = 
    | Project of string list
    | SetTo of string * expr
  [@@deriving sexp, compare]
end

module JoinExp = struct
  type t = ((string * string) * string) list

  let in_match (a1, a2) (b1, b2) = 
    String.(a1 = b1 && a2 = b2)

  let eval (e : t) a = 
    List.find_map e ~f:(fun (b, out) -> 
      if in_match a b then 
        Some out
      else None)

  let eval_exn e (a1, a2) = 
    eval e (a1, a2) 
    |> Option.value_exn ~message:("couldn't evaluate (" ^ a1 ^ ", " ^ a2 ^ ")")
  
  let wf xs ys zs e = 
    List.for_all2_exn xs ys ~f:(fun x y -> 
      match eval e (x, y)  with 
      | None -> false
      | Some z -> List.exists zs ~f:(String.(=) z) 
    )

  let out_actions (e : t) : string list = 
    List.map e ~f:snd

end

module Clause = struct
  type f = Symbol.t [@@deriving sexp, compare]
  type t =
    | Id of f
    | Join of f * f * (((string * string) * string) list)
    | Compose of f * f
    | MapOut of f * ActionTfx.t
    | MapIn of f * MatchTfx.t
    | Inverse of f
  [@@deriving sexp, compare]

  let insert_eval config table provrow idx =
    function 
    | Id f when Symbol.(f = table) -> 
      [ProvRow.add provrow table idx]
    | MapOut (f,_) when Symbol.(f = table) -> 
      failwith "todo"
    | MapIn (f,_) when Symbol.(f = table) ->
      failwith "todo"
    | Inverse f when Symbol.(f = table) -> 
      let rows = ProvRow.op provrow in 
      List.map rows ~f:(fun row -> ProvRow.add row table idx)
    | Join (f, g, merge) when Symbol.(f = table || g = table) -> 
      let open Semantics in 
      let other = if Symbol.(f = table) then g else f in 
      let other_table : ProvTable.t = Config.find_exn config other in 
      List.fold other_table.rows ~init:[] ~f:(fun delta other -> 
        match MatchAction.pair provrow.row other.row ~f:(JoinExp.eval_exn merge) with
        | None -> delta
        | Some row ->
          delta @ [{provrow with 
            prov = Provenance.union provrow.prov other.prov; 
            row;
          }]
      )
    | Compose (f, other) when Symbol.(f = table) ->
      let output = provrow.row.action.args in
      let other_table = Config.find_exn config other in 
      let other_rows = ProvTable.matching_rows other_table output in
      List.map other_rows ~f:(fun other_row -> 
        {provrow with
          row = Semantics.MatchAction.make provrow.row.matches other_row.row.action;
          prov = Provenance.(add provrow.loc (add other_row.loc (union provrow.prov other_row.prov)))
        }
      )
    | Compose (other, g) when Symbol.(g = table) ->
      let other_table = Config.find_exn config other in 
      let other_rows = ProvTable.preimage_rows other_table provrow.row in
      List.map other_rows ~f:(fun other_row -> 
        {provrow with 
          row = Semantics.MatchAction.make other_row.row.matches provrow.row.action;
          prov = Provenance.(add provrow.loc (add other_row.loc (union provrow.prov other_row.prov)))
        }
      )
    | _ -> 
      (*No changes, insertion doesnt affect the current row *)
      []
end

type t = {defined : Symbol.t; definition : Clause.t } [@@deriving sexp, compare]

let table_indices table = List.filter_map  ~f:(fun (tbl,idx) -> 
  if Symbol.(table = tbl) then 
    Some idx
  else
    None
)

let priority how config (row1 : ProvRow.t) (row2 : ProvRow.t) =
  let prov1 = row1.prov |> Option.value_exn ~message:"tried to compare provenances, but prov1 had none" in 
  let prov2 = row2.prov |> Option.value_exn ~message:"tried to compare provenances, but prov2 had none" in 
  let tables = Config.get_tables config in 
  let indices1 = List.map prov1 ~f:(Config.get_index config)in
  let indices2 = List.map prov2 ~f:(Config.get_index config) in
  List.for_all tables ~f:(fun table -> 
    let tbl_indices1 = table_indices table indices1 in 
    let tbl_indices2 = table_indices table indices2 in 
    List.for_all tbl_indices1 ~f:(fun i -> 
      List.for_all tbl_indices2 ~f:(fun j -> 
        match how with
        | `Higher -> i > j
        | `Lower -> i < j
      )
    )
  )

let add_to_table config (table : ProvTable.t) (new_row : ProvRow.t) = 
  let above,below = 
    List.foldi table.rows ~init:([],[]) ~f:(fun i (above, below) prov_row -> 
      if Semantics.MatchAction.empty_intersection prov_row.row new_row.row then 
        (above,below)
      else if priority `Higher config new_row prov_row then
        (above@[i],below)
      else if priority `Lower config new_row prov_row then
        (above, i::below)
      else
        failwith "Provenance Resolution Error: Provenances were equal or incomparable"
    )
  in
  if Provenance.consistent_partition above below ~equal:Int.equal then
    let max_above_index = List.max_elt ~compare:Int.compare above |> Option.value ~default:0 in 
    ProvTable.insert ~into:table ~after:max_above_index new_row.row new_row.prov
  else
    failwith "inconsistent partition on insertion"

let add_many_to_table config symbol delta =
  let table =  Config.find_exn config symbol in
  List.fold delta ~init:table ~f:(fun table row -> 
    add_to_table config table row
  )
  |> Config.set config symbol

let insert {defined; definition} config table provrow idx =
  Clause.insert_eval config table provrow idx definition
  |> add_many_to_table config defined



let delete config loc = Config.remove config [loc]


