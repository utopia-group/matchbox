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
  | BVHole
  | Var of string
  | Incr of bvexp
  | Decr of bvexp

let rec bvexp_to_string = function 
  | BVHole -> "?"
  | Var x -> x
  | Incr b -> Printf.sprintf "(incr %s)" (bvexp_to_string b)
  | Decr b -> Printf.sprintf "(decr %s)" (bvexp_to_string b)

let rec bvexp_vars = function
  | BVHole -> []
  | Var x -> [x]
  | Incr d | Decr d -> bvexp_vars d

let rec bvexp_equal b1 b2 =
  match b1, b2 with 
  | BVHole, BVHole -> true
  | Var x, Var y -> String.(x = y)
  | Incr b1, Incr b2 
  | Decr b1, Decr b2 -> 
    bvexp_equal b1 b2 
  | _, _ -> false

let rec bv_eval (valuation : int String.Map.t) (b : bvexp) =
  match b with 
  | BVHole -> failwith "cannot evaluate hole"
  | Var x -> String.Map.find_exn valuation x
  | Incr b -> bv_eval valuation b + 1
  | Decr b -> bv_eval valuation b - 1

let rec bv_set_eval (valuation : Match.t String.Map.t) (b : bvexp) = 
  match b with 
  | BVHole -> failwith "cannot evaluate hole"
  | Var x -> String.Map.find_exn valuation x
  | Incr b -> bv_set_eval valuation b |> Match.incr
  | Decr b -> bv_set_eval valuation b |> Match.decr

type rowexp =
  | RHole
  | Id 
  | RenameActionTo of string
  | DataSlice of string list
  | MapKey of string * string list * bvexp
  | MapData of string * string list * bvexp
  | Pipe of rowexp * rowexp

let rename_action_to s = RenameActionTo s
let data_slice ps = DataSlice ps

let rec rowexp_to_string = function 
  | RHole -> "?"
  | Id -> "Id"
  | RenameActionTo a -> Printf.sprintf "RenameActionTo %s" a
  | DataSlice ps -> Printf.sprintf "DataSlice %s" (String.concat ps ~sep:":")
  | MapKey (key, from, b) -> Printf.sprintf "MapKey (%s,%s,%s)" key (String.concat from ~sep:",") (bvexp_to_string b)
  | MapData (key, from, b) -> Printf.sprintf "MapData (%s,%s,%s)" key (String.concat from ~sep:",") (bvexp_to_string b) 
  | Pipe (r1, r2) -> Printf.sprintf "Pipe(%s, %s)" (rowexp_to_string r1) (rowexp_to_string r2)

let rec rowexp_equal r1 r2 =
  match r1, r2 with 
  | RHole, RHole | Id, Id -> true
  | RenameActionTo s1, RenameActionTo s2 -> String.(s1 = s2)
  | DataSlice ps1, DataSlice ps2 -> List.equal String.equal ps1 ps2
  | MapKey (lvalue1, params1, b1), MapKey (lvalue2, params2, b2) 
  | MapData (lvalue1, params1, b1), MapKey(lvalue2, params2, b2) -> 
    String.(lvalue1 = lvalue2) && List.equal String.equal params1 params2 && bvexp_equal b1 b2
  | Pipe (r1, r2), Pipe(r1', r2') -> rowexp_equal r1 r1' && rowexp_equal r2 r2'
  | _, _ -> false

let rec rexp_size = function
  | RHole | Id -> 0
  | RenameActionTo _ -> 1
  | DataSlice _ -> 1
  | MapKey _ -> 2
  | MapData _ -> 2
  | Pipe (r1, r2) -> rexp_size r1 + 1 +  rexp_size r2


let rec rexp_hole_free = function 
  | RHole -> false
  | Id | RenameActionTo _ | DataSlice _ | MapKey _ | MapData _ -> true
  | Pipe (r1, r2) -> 
    rexp_hole_free r1 && rexp_hole_free r2

let rec r_eval (r : rowexp) (row : MatchAction.t) =
  match r with
  | RHole -> failwith "cannot evaluate row expression holes"
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
  | EHole
  | Table of string
  | Map of (exp * rowexp)
  | Compose of exp * exp
  | Case of { 
    table : exp; 
    callbacks : rowexp String.Map.t option
    (* None corresponds to a hole*)
  }

let rec exp_equiv e1 e2 =
  match e1, e2 with 
  | EHole, EHole -> true
  | Table t1, Table t2 -> String.(t1 = t2)
  | Map (e1, r1), Map (e2, r2) -> 
    exp_equiv e1 e2 && rowexp_equal r1 r2
  | Compose (e1, e2), Compose (e1', e2') -> 
    exp_equiv e1 e1' && exp_equiv e2 e2'
  | Case case1, Case case2 -> 
    exp_equiv case1.table case2.table
    && Option.equal (String.Map.equal rowexp_equal) case1.callbacks case2.callbacks
  | _, _ -> false

let rec exp_to_string = function
  | EHole -> "?"
  | Table t -> t
  | Map (e, r) -> Printf.sprintf "Map(%s,%s)" (exp_to_string e) (rowexp_to_string r)
  | Compose (e1, e2) -> Printf.sprintf "Compose(%s, %s)" (exp_to_string e1) (exp_to_string e2)
  | Case {table;callbacks = None} -> 
    Printf.sprintf "Case(%s, ?)" (exp_to_string table)
  | Case {table;callbacks = Some callbacks} ->
    (String.Map.fold callbacks ~init:"" ~f:(fun ~key ~data acc -> Printf.sprintf "%s, %s->%s" acc key (rowexp_to_string data)))
    |> Printf.sprintf "Case(%s%s)" (exp_to_string table) 

let rec exp_size = function 
  | EHole -> 0 
  | Table _ -> 1
  | Map (e, r) -> exp_size e + 1 + rexp_size r
  | Compose (e1, e2) -> exp_size e1 + exp_size e2
  | Case {table; callbacks} -> 
    match callbacks with 
    | None -> exp_size table + 1
    | Some callbacks -> 
      exp_size table + 
      String.Map.fold callbacks ~init:1 
        ~f:(fun ~key:_ ~data acc -> 
          rexp_size data + acc
        )

let rec exp_hole_free = function
  | EHole | Case {callbacks=None; _} -> false
  | Table _ -> true
  | Map (e, r) -> exp_hole_free e && rexp_hole_free r
  | Compose (e1, e2) -> exp_hole_free e1 && exp_hole_free e2
  | Case {table; callbacks = Some callbacks} ->
    exp_hole_free table && 
    String.Map.for_all callbacks ~f:(rexp_hole_free)

let rec e_eval (valuation : Value.t String.Map.t) (e : exp) : Value.t =
  match e with 
  | EHole | Case {callbacks = None;_} -> failwith "cannot evaluate holes"
  | Table x -> 
    String.Map.find_exn valuation x
  | Map (exp, rexp) ->
    let tbl = e_eval valuation exp in
    Value.map tbl ~f:(r_eval rexp)
  | Compose (e1, e2) -> 
    let tbl1 = e_eval valuation e1 in 
    let tbl2 = e_eval valuation e2 in 
    Value.compose tbl1 tbl2
  | Case {table; callbacks = Some callbacks} -> 
    let t = e_eval valuation table in 
    let f (ma : MatchAction.t) : MatchAction.t = 
      let action_name = Action.get_name ma.action in
      let callback = String.Map.find_exn callbacks action_name in
      r_eval callback ma
    in
    Value.map t ~f

type t = 
  | Assign of { table: string; from : string list; body : exp }
  | Seq of t list

let rec hole_free = function 
  | Assign a -> exp_hole_free a.body
  | Seq cs -> List.for_all cs ~f:hole_free

let rec run (cfg : Config.t) : t -> Config.t = function 
  | Assign {table; from; body} -> 
    let cfg' = String.Map.filter_keys cfg ~f:(List.mem from ~equal:String.equal) in 
    String.Map.set cfg ~key:table ~data:(e_eval cfg' body)
  | Seq cs -> 
    List.fold cs ~init:cfg ~f:run

let case' tablename actions = 
  Case {
    table = Table tablename;
    callbacks = Some (String.Map.of_alist_exn actions)
  }


let find queue ~f ~extend ~pop ~add_all = 
  let rec loop queue = 
    match pop queue with 
    | None -> None
    | Some (p, _) when f p -> 
      Some p 
    | Some (p, queue) -> 
      extend p
      |> add_all queue
      |> loop
    in
  loop queue