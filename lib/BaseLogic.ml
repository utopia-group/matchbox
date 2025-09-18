open Core

module Var = Gpl.Var

module Symbol = struct
  type t = {name : string; ins : int list; out : int} [@@deriving sexp, compare]
  let make name ins out = {name; ins; out}
  let (=) f g = String.(f.name = g.name)

  let to_string symbol = symbol.name

end

module Config = struct 
  open Semantics
  module Table = MatchActionTable
  type t = {
    symbols : Symbol.t list;
    cfg : Table.t String.Map.t;
  }

  let _find_raw_exn cfg x = Map.find_exn cfg.cfg x

  let find_exn cfg (symbol : Symbol.t) : Table.t =
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

end


module MatchTfx = struct
  open Gpl
  open Semantics

  type t = 
    | Del of Var.t
    | WildCard of Var.t
    | Project of Var.t list
    | SetTo of Var.t * Expr.t
    | CubeFilter of MatchExpression.t
    | Filter of BExpr.t
end

module OutTfx = struct
  open Gpl
  open Semantics
  type t = 
    | Nonce of Var.t
    | Del of Var.t
    | Project of Var.t list
    | SetTo of Var.t * Expr.t
    | Rename of MagmaAction.t * MagmaAction.t
end

module Clause = struct
  type f = Symbol.t [@@deriving sexp, compare]
  type t =
    | Id of f * Type.t option
    | Table of Semantics.MatchActionTable.t * Type.t option
    | Join of t * t * Type.t option
    | Compose of t * t * Type.t option
    | MapOut of t * OutTfx.t * Type.t option
    | MapIn of t * MatchTfx.t * Type.t option

  let typeof_exn = function 
    | Id (_, Some t)
    | Table (_, Some t)
    | Join (_, _, Some t)
    | Compose (_, _, Some t)
    | MapOut (_, _, Some t)
    | MapIn (_, _, Some t) -> 
      Type.get_table_exn t
    | _ -> 
      failwith "[typeof_exn] Couldn't deduce type"

  let id f = Id (f, None)
  let join c1 c2 = Join (c1, c2, None)
  let ( * ) = join

  let compose c1 c2 = Compose (c1, c2, None)
  let (>>>) = compose
  let mapout c tfx = MapOut (c, tfx, None)
  let (|>>) = mapout
  let mapin c tfx = MapIn (c, tfx, None)
  let (<<|) tfx c = mapin c tfx

  let table mat = Table(mat, None)

end

type t = {defined : Symbol.t; definition : Clause.t }

(* Encodings of Fig. 2 transformations via BaseLogic.t list *)

(* let project in_symbol fields mid_symbol out_symbol =
  [
    {defined = mid_symbol; definition = Clause.MapIn (in_symbol, MatchTfx.Project fields)};
    {defined = out_symbol; definition = Clause.MapOut (mid_symbol, ActionTfx.Project fields)}
  ]

let filter in_symbol matches mid_symbol out_symbol =
  [
    {defined = mid_symbol; definition = Clause.MapIn (in_symbol, MatchTfx.Filter matches)};
    {defined = out_symbol; definition = Clause.MapOut (mid_symbol, ActionTfx.Filter matches)}
  ]

let table_symbol in_symbol out_symbol = 
  [{defined = out_symbol; definition = Clause.Id in_symbol}]

let compose in_symbol1 in_symbol2 out_symbol =
  [{defined = out_symbol; definition = Clause.Compose (in_symbol1, in_symbol2)}]

let join in_symbol1 out_symbol2 alignment out_symbol =
  [{defined = out_symbol; definition = Clause.Join (in_symbol1, out_symbol2, alignment)}]

let invert in_symbol out_symbol =
  [{defined = out_symbol; definition = Invert in_symbol}]

let rename_key in_symbol old_name new_name out_symbol =
  [{defined = out_symbol; definition = Clause.MapIn (in_symbol, MatchTfx.SetTo (old_name, Var new_name))}]

let rename_action in_symbol old_name new_name out_symbol =
  [{defined = out_symbol; definition = Clause.MapOut (in_symbol, ActionTfx.SetTo (old_name, Var new_name))}]

let write_data in_symbol action_name action_data out_symbol =
  [{defined = out_symbol; definition = Clause.MapOut (in_symbol, ActionTfx.SetTo (action_name, Data action_data))}]

let write_key in_symbol match_name _match out_symbol =
  [{defined = out_symbol; definition = Clause.MapIn (in_symbol, MatchTfx.SetTo (match_name, Match _match))}] *)

module TransformExpr = struct
  type hardware = CAM | LPM | TCAM

  (* Mapping pairs of action names to transformed action name *)
  type key_alignment = ((string * string) * string) list

  type field_renaming = (string * string) list

  type assignment = (string * Bit.Vector.t) list

  type t = 
    | TableLiteral of Semantics.MatchActionTable.t
    | TableSymbol of Symbol.t
    | Compose of t * t
    | Join of t * t * key_alignment
    | Project of t * string list
    | Filter of t * Semantics.Match.t Map.M(String).t
    | RenameKeys of t * field_renaming
    | RenameActions of t * field_renaming
    | Invert of t
    | WriteData of t * assignment
    | WriteKey of t * assignment

  let key_alignment_to_string alignment =
    let mapped = List.map alignment ~f:(fun ((f1, f2), out) -> sprintf "(%s,%s) |-> %s" f1 f2 out) in
    let joined = String.concat ~sep:", " mapped in
    sprintf "{%s}" joined

  let field_renaming_to_string renaming =
    let mapped = List.map renaming ~f:(fun (old_name, new_name) -> sprintf "%s |-> %s" old_name new_name) in
    let joined = String.concat ~sep:", " mapped in
    sprintf "{%s}" joined

  let assignment_to_string assignments =
    let mapped = List.map assignments ~f:(fun (field, bv) -> sprintf "%s := %s" field (Bit.Vector.to_string bv)) in
    let joined = String.concat ~sep:", " mapped in
    sprintf "{%s}" joined

  let rec to_string = function
    | TableLiteral _ -> "<table>" (* Could be more detailed *)
    | TableSymbol symbol -> Symbol.to_string symbol
    | Compose (c1, c2) -> sprintf "(%s >>> %s)" (to_string c1) (to_string c2)
    | Join (c1, c2, alignment) -> 
        sprintf "join(%s, %s) by %s" 
          (to_string c1) (to_string c2) (key_alignment_to_string alignment)
    | Project (c, fields) ->
        sprintf "project %s keeping {%s}" 
          (to_string c) (String.concat ~sep:", " fields)
    | Filter (c, matches) ->
        let match_strs = Map.to_alist matches |> List.map ~f:(fun (field, mtch) ->
          sprintf "%s: %s" field (Semantics.Match.to_string mtch)) in
        sprintf "filter %s where {%s}" 
          (to_string c) (String.concat ~sep:", " match_strs)
    | RenameKeys (c, renaming) ->
        sprintf "rename %s keys %s" 
          (to_string c) (field_renaming_to_string renaming)
    | RenameActions (c, renaming) ->
        sprintf "rename %s actions %s" 
          (to_string c) (field_renaming_to_string renaming)
    | Invert c ->
        sprintf "invert %s" (to_string c)
    | WriteData (c, assignments) ->
        sprintf "write %s data %s" 
          (to_string c) (assignment_to_string assignments)
    | WriteKey (c, assignments) ->
        sprintf "write %s key %s" 
          (to_string c) (assignment_to_string assignments)

  let table_literal mat = TableLiteral mat
  let table_symbol name = TableSymbol name
  let compose c1 c2 = Compose (c1, c2)
  let join c1 c2 alignment = Join (c1, c2, alignment)
  let project c fields = Project (c, fields)
  let filter c pred = Filter (c, pred)
  let rename_keys c renaming = RenameKeys (c, renaming)
  let rename_actions c renaming = RenameActions (c, renaming)
  let invert c = Invert c
  let write_data c assignments = WriteData (c, assignments)
  let write_key c assignments = WriteKey (c, assignments)

  let ( >>> ) c1 c2 = compose c1 c2
end

module SurfaceLogic = struct
  type t = {
    defined : Symbol.t;
    definition : TransformExpr.t
  }

  let to_string {defined; definition} =
    sprintf "%s o-- %s" defined.name (TransformExpr.to_string definition)

  let define_table symbol expr = {defined = symbol; definition = expr}
end
