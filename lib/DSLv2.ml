open Core
open Semantics

module Value = struct
  include MatchActionTable

  let compose (t1 : t) (t2 : t) : t =
    List.map t1 ~f:(fun r1 -> 
      let keys = r1.action.args in
      let action = run t2 keys in 
      {r1 with action}
    )

  let bind (tbl : t) ~(f : MatchAction.t -> t) : t = List.bind tbl ~f

  let fold (tbl : t) = List.fold tbl

  let empty : t = []

end

module Config = struct 
  type t = Value.t String.Map.t
  let equal = String.Map.equal Value.equal

  let to_string : t -> string = 
    String.Map.fold ~init:"" ~f:(fun ~key ~data acc -> 
      Printf.sprintf "%s%stable %s->\n%s\n----------------------------"
        acc
        (if String.equal acc "" then "" else "\n")
        key
        (Value.to_string data)
    )

end

type bvexp = 
  | Var of string
  | Incr of bvexp
  | Decr of bvexp

let rec bv_eval (valuation : int String.Map.t) (b : bvexp) =
  match b with 
  | Var x -> String.Map.find_exn valuation x
  | Incr b -> bv_eval valuation b + 1
  | Decr b -> bv_eval valuation b - 1

let rec bv_set_eval (valuation : Match.t String.Map.t) (b : bvexp) = 
  match b with 
  | Var x -> String.Map.find_exn valuation x
  | Incr b -> bv_set_eval valuation b |> Match.incr
  | Decr b -> bv_set_eval valuation b |> Match.decr

type rowexp =
  | Id
  | RenameActionTo of string
  | DataSlice of string list
  | MapKey of string * string list * bvexp
  | MapData of string * string list * bvexp
  | Pipe of rowexp * rowexp

let rec r_eval (r : rowexp) (row : MatchAction.t) =
  match r with
  | Id -> row
  | RenameActionTo name -> 
    {row with action = Action.set_name name row.action}
  | DataSlice params ->
    {row with action = Action.project_data params row.action}
  | Pipe (r1, r2) -> 
    r_eval r1 row
    |> r_eval r2
  | MapData (x, params, bv_exp) -> 
    let args = List.map params ~f:(fun x -> (x, Action.get_data row.action x)) |> String.Map.of_alist_exn in
    let b = bv_eval args bv_exp in
    {row with action = Action.update_data row.action x b}
  | MapKey (x, params, bv_exp) -> 
    let args = List.map params ~f:(fun x -> (x, MatchAction.get_match row x)) |> String.Map.of_alist_exn in
    let b = bv_set_eval args bv_exp in
    {row with matches = String.Map.set row.matches ~key:x ~data:b}
    

type exp = 
  | Table of string
  | Map of (exp * rowexp)
  | Compose of exp * exp
  | Case of { table : exp; callbacks : rowexp String.Map.t }

let rec e_eval (valuation : Value.t String.Map.t) (e : exp) : Value.t =
  match e with 
  | Table x -> 
    String.Map.find_exn valuation x
  | Map (exp, rexp) ->
    let tbl = e_eval valuation exp in
    Value.map tbl ~f:(r_eval rexp)
  | Compose (e1, e2) -> 
    let tbl1 = e_eval valuation e1 in 
    let tbl2 = e_eval valuation e2 in 
    Value.compose tbl1 tbl2
  | Case {table; callbacks} -> 
    let t = e_eval valuation table in 
    let f (ma : MatchAction.t) : MatchAction.t = 
      let action_name = Action.get_name ma.action in
      let callback = String.Map.find_exn callbacks action_name in
      r_eval callback ma
    in
    Value.map t ~f


type t = 
  | Assign of { table: string; from : string list;  body : exp}
  | Seq of t list

let rec run (cfg : Config.t) : t -> Config.t = function 
  | Assign {table; from; body} -> 
    let cfg' = String.Map.filter_keys cfg ~f:(List.mem from ~equal:String.equal) in 
    String.Map.set cfg ~key:table ~data:(e_eval cfg' body)
  | Seq cs -> 
    List.fold cs ~init:cfg ~f:run
