open Core

module type Primitive = sig
  type t [@@deriving equal]
  val assume : BExpr.t -> t
  val assert_ : BExpr.t -> t
  val to_smtlib : t -> string
end

let substitution_of facts x =
  match Map.find facts x with
  | None -> Expr.var x
  | Some e -> e

module Assert = struct
  type t = BExpr.t [@@deriving equal]

  let assert_ (phi : BExpr.t) : t = phi
  let to_smtlib (asst : t) =
    Printf.sprintf "assert %s" (BExpr.to_smtlib asst)
end

module Assume = struct
  type t = BExpr.t [@@deriving equal]

  let assume (phi: BExpr.t) = phi
  let to_smtlib (assm : t) =
    Printf.sprintf "assume %s" (BExpr.to_smtlib assm)
end

module Passive = struct
  type t =
    | Assume of Assume.t
    | Assert of Assert.t
    [@@deriving equal]

  let assume b = Assume (Assume.assume b)
  let assert_ a = Assert (Assert.assert_ a)

  let to_smtlib = function 
    | Assume phi -> Assume.to_smtlib phi
    | Assert phi -> Assert.to_smtlib phi

end

module Assign = struct
  type t = Var.t * Expr.t [@@deriving equal]

  let to_smtlib (x,e) = Printf.sprintf "%s:=%s" (Var.str x) (Expr.to_smtlib e)

  let name _ = "assign"

  let assign x e = (x,e)

end

module Active = struct
  type t =
    | Passive of Passive.t
    | Assign of Assign.t
    [@@deriving equal]

  let passive (p : Passive.t) : t = Passive p
  let assume b = passive (Passive.assume b)

  let assert_ b = passive (Passive.assert_ b)
  let assign_ a = Assign a
  let assign x e = assign_ (Assign.assign x e)

  let to_smtlib active =
    match active with
    | Passive p -> Passive.to_smtlib p
    | Assign a -> Assign.to_smtlib a


end


module Action = struct
  include Active

end

module Table = struct
  type kind = 
  | Exact
  | Maskable
  | MaskableDegen
  [@@deriving eq]


  type t = {name : string;
            keys : (Var.t * kind) list;
            actions : (Var.t list * Action.t list) list;
           } [@@deriving eq]


  let make name keys actions = {name; keys; actions}

  let to_smtlib tbl = Printf.sprintf "%s.apply(){%s}" tbl.name @@
    List.fold tbl.actions ~init:"" ~f:(fun acc (params, commands) ->
        Printf.sprintf "%s\n\t\\%s -> {%s\t}" acc (Var.list_to_smtlib_quant params) @@
        List.fold commands ~init:"\n" ~f:(fun acc a ->
            Printf.sprintf "%s\t\t%s\n" acc (Action.to_smtlib a)
          )
      )
end

module Pipeline = struct
  type t =
    | Active of Active.t
    | Table of Table.t
    [@@deriving equal]

  let active a = Active a
  let assign x e = active @@ Active.assign x e

  let action (a : Action.t) = Active a

  let table name keys actions =
    Table (Table.make name keys actions)

  let to_smtlib = function
    | Active a -> Active.to_smtlib a
    | Table t -> Table.to_smtlib t

  let assume b = Active (Active.assume b)
  let assert_ b = Active (Active.assert_ b)

end
