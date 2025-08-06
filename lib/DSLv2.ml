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

  let restrict keys cfg =
    String.Map.filter_keys cfg ~f:(List.mem ~equal:String.equal keys)

  let to_string : t -> string = 
    String.Map.fold ~init:"" ~f:(fun ~key ~data acc -> 
      Printf.sprintf "%s%stable %s->\n%s\n----------------------------"
        acc
        (if String.equal acc "" then "" else "\n")
        key
        (Value.to_string data)
    )

end

type skolems = ((Trit.Vector.t list * Bit.Vector.t) list * int) String.Map.t

type bvexp = 
  | BVHole
  | Var of (string * int)
  | Lit of Bit.Vector.t
  | Fun of (string * string list * int)
  | Incr of bvexp
  | Decr of bvexp

let rec bvexp_to_string = function 
  | BVHole -> "?"
  | Var (x, _) -> x
  | Lit bv -> Bit.Vector.to_string bv
  | Fun (f, xs, w) -> Printf.sprintf "%s(%s)#%d" f (String.concat xs ~sep:",") w
  | Incr b -> Printf.sprintf "(incr %s)" (bvexp_to_string b)
  | Decr b -> Printf.sprintf "(decr %s)" (bvexp_to_string b)

let rec bvexp_vars = function
  | BVHole | Lit _ -> []
  | Var (x,_) -> [x]
  | Fun (_, xs, _) -> xs
  | Incr d | Decr d -> bvexp_vars d

let rec bvexp_width = function 
  | BVHole -> failwith "Cannot compute width of unknown"
  | Var (_, w) | Fun (_, _, w) -> w
  | Lit bv ->  Bit.Vector.length bv
  | Incr e | Decr e -> bvexp_width e

let rec bvexp_equal b1 b2 =
  match b1, b2 with 
  | BVHole, BVHole -> true
  | Lit v1, Lit v2 -> Bit.Vector.equal v1 v2
  | Fun (f, xs, w), Fun (g, ys, l) -> String.(f = g && List.equal (=) xs ys) && w = l
  | Var (x,_), Var (y,_) -> String.(x = y)
  | Incr b1, Incr b2 
  | Decr b1, Decr b2 -> 
    bvexp_equal b1 b2 
  | _, _ -> false 

let skolem_run (funcs : skolems) (f : string) (width : int) (args : Trit.Vector.t list) : Bit.Vector.t * skolems =
  match String.Map.find funcs f with 
  | None -> 
    let value = Bit.Vector.zero width in 
    let data = [args, value], 0 in 
    let funcs = String.Map.add_exn funcs ~key:f ~data in 
    (value, funcs)
  | Some (mapping, max) -> 
    match List.find mapping ~f:(fun (tvs, _) -> List.equal Trit.Vector.equal tvs args) with 
    | None -> 
      let max' = max + 1 in 
      if Float.(of_int max' >= (2. ** of_int width)) then 
        failwithf "PIDGEONHOLE: Output type of %s was bit<%d>, but tried to map %d different inputs" f width max' ();
      let max_bv' = Bit.Vector.of_int ~width max' in 
      let mapping' = mapping @ [args, max_bv'] in 
      let data = mapping', max' in 
      let funcs' = String.Map.set funcs ~key:f ~data in 
      (max_bv', funcs')
    | Some (_, bv) -> 
      (bv, funcs)

(* let rec  (funcs : skolems) (valuation : Bit.Vector.t String.Map.t) (b : bvexp) : Bit.Vector.t * skolems =
  match b with 
  | BVHole -> failwith "cannot evaluate hole"
  | Var x -> (String.Map.find valuation x |> Option.value_exn ~message:("Couldn't find " ^ x), funcs)
  | Lit bv -> (bv, funcs)
  | Fun (f,xs,w) -> 
    skolem_run funcs f w (List.map xs ~f:(String.Map.find_exn valuation))
  | Incr b -> Tuple2.map_fst (bv_eval funcs valuation b) ~f:Bit.Vector.incr
  | Decr b -> Tuple2.map_fst (bv_eval funcs valuation b) ~f:Bit.Vector.decr
 *)
let rec bv_set_eval (funcs : skolems) (valuation : Match.t String.Map.t) (b : bvexp) =
  let open List in  
  match b with 
  | BVHole -> failwith "cannot evaluate hole"
  | Var (x, _) -> 
    let mtch = String.Map.find valuation x |> Option.value_exn ~message:("Couldn't find " ^ x) in 
    [mtch], funcs
  | Lit bv -> [Exact bv], funcs
  | Fun (f, xs, w) -> 
    let bv,funcs = (xs >>| String.Map.find_exn valuation) >>| Match.get_tv |> skolem_run funcs f w in 
    [Exact bv], funcs
  | Incr b -> 
    let matches, funcs = bv_set_eval funcs valuation b in 
    matches >>= Match.incr, funcs
  | Decr b -> 
    let matches, funcs = bv_set_eval funcs valuation b in 
    matches >>= Match.decr, funcs

let bv_eval funcs valuation b =
(*   let match_valuation = String.Map.map valuation ~f:(fun bv -> Match.Exact bv) in *)
  let set, funcs = bv_set_eval funcs valuation b in 
  match set with
  | [mtch] -> Match.(get_exact (to_exact mtch)), funcs
  | _ -> failwith "tried to evaluate a bv_expression as a raw bitvector, but got multiple values"

type rowexp =
  | RHole
  | Id 
  | RenameActionTo of string
  | DataSlice of string list
  | KeySlice of string list
  | MapKey of string * string list * bvexp
  | MapData of string * string list * bvexp
  | Pipe of rowexp * rowexp

let rename_action_to s = RenameActionTo s
let data_slice ps = DataSlice ps
let data_slice' ps' = List.map ps' ~f:fst |> data_slice

let rec rowexp_to_string = function 
  | RHole -> "?"
  | Id -> "Id"
  | RenameActionTo a -> Printf.sprintf "RenameActionTo %s" a
  | DataSlice ps -> Printf.sprintf "DataSlice [%s]" (String.concat ps ~sep:",")
  | KeySlice ps -> Printf.sprintf "KeySlice [%s]" (String.concat ps ~sep:",")
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
  | DataSlice _ | KeySlice _-> 1
  | MapKey _ -> 2
  | MapData _ -> 2
  | Pipe (r1, r2) -> rexp_size r1 + 1 +  rexp_size r2


let rec rexp_hole_free = function 
  | RHole -> false
  | Id | RenameActionTo _ | DataSlice _ | MapKey _ | MapData _ | KeySlice _-> true
  | Pipe (r1, r2) -> 
    rexp_hole_free r1 && rexp_hole_free r2

let rec r_eval (funcs : skolems) (r : rowexp) (row : MatchAction.t) : MatchAction.t list * skolems =
  match r with
  | RHole -> failwith "cannot evaluate row expression holes"
  | Id -> [row], funcs
  | RenameActionTo name -> 
    [{row with action = Action.set_name name row.action}], funcs
  | DataSlice params ->
    [{row with action = Action.project_data params row.action}], funcs
  | KeySlice keys -> 
    [MatchAction.restrict_keys row keys], funcs
  | Pipe (r1, r2) -> 
    let ms1, funcs = r_eval funcs r1 row in 
    List.fold ms1 ~init:([], funcs) ~f:(fun (m2s, funcs) row -> 
      let m2, funcs = r_eval funcs r2 row in 
      m2s @ m2, funcs  
    )
  | MapData (x, params, bv_exp) -> 
    let args = List.map params ~f:(fun x -> 
      (x, MatchAction.get_field row x)) 
    |> String.Map.of_alist_exn in
    let b, funcs = bv_eval funcs args bv_exp in
    let action = Action.update_data row.action x b in 
    [{row with action}], funcs
  | MapKey (x, params, bv_exp) -> 
    let args = List.map params ~f:(fun x -> (x, MatchAction.get_match row x)) |> String.Map.of_alist_exn in
    let matches, funcs = bv_set_eval funcs args bv_exp in 
    List.map matches ~f:(fun b -> 
      {row with matches = String.Map.set row.matches ~key:x ~data:b}
    ), funcs
    

type exp = 
  | EHole
  | Literal of MatchActionTable.t
  | Table of string
  | Map of (exp * rowexp)
(*   | Compose of exp * exp *)
  | Case of { 
    table : string; 
    callbacks : rowexp String.Map.t option
    (* None corresponds to a hole*)
  }

let rec exp_equiv e1 e2 =
  match e1, e2 with 
  | EHole, EHole -> true
  | Table t1, Table t2 -> String.(t1 = t2)
  | Map (e1, r1), Map (e2, r2) -> 
    exp_equiv e1 e2 && rowexp_equal r1 r2
(*   | Compose (e1, e2), Compose (e1', e2') -> 
    exp_equiv e1 e1' && exp_equiv e2 e2' *)
  | Case case1, Case case2 -> 
    String.equal case1.table case2.table
    && Option.equal (String.Map.equal rowexp_equal) case1.callbacks case2.callbacks
  | _, _ -> false

let rec exp_to_string = function
  | EHole -> "?"
  | Table t -> t
  | Literal table -> MatchActionTable.to_string table
  | Map (e, r) -> Printf.sprintf "Map(%s,%s)" (exp_to_string e) (rowexp_to_string r)
(*   | Compose (e1, e2) -> Printf.sprintf "Compose(%s, %s)" (exp_to_string e1) (exp_to_string e2) *)
  | Case {table;callbacks = None} -> 
    Printf.sprintf "Case(%s, ?)" table
  | Case {table;callbacks = Some callbacks} ->
    (String.Map.fold callbacks ~init:"" ~f:(fun ~key ~data acc -> Printf.sprintf "%s, %s->%s" acc key (rowexp_to_string data)))
    |> Printf.sprintf "Case(%s%s)" table

let rec exp_size = function 
  | EHole -> 0 
  | Table _ -> 1
  | Literal table -> MatchActionTable.size table
  | Map (e, r) -> exp_size e + 1 + rexp_size r
(*   | Compose (e1, e2) -> exp_size e1 + exp_size e2 *)
  | Case {table=_; callbacks} -> 
    match callbacks with 
    | None -> 1
    | Some callbacks -> 
      1 + 
      String.Map.fold callbacks ~init:1 
        ~f:(fun ~key:_ ~data acc -> 
          rexp_size data + acc
        )

let rec exp_hole_free = function
  | EHole | Case {callbacks=None; _} -> false
  | Table _ | Literal _ -> true
  | Map (e, r) -> exp_hole_free e && rexp_hole_free r
(*   | Compose (e1, e2) -> exp_hole_free e1 && exp_hole_free e2 *)
  | Case {table=_; callbacks = Some callbacks} -> 
    String.Map.for_all callbacks ~f:(rexp_hole_free)

let rec e_eval (funcs : skolems) (valuation : Value.t String.Map.t) (e : exp) : Value.t * skolems =
  match e with 
  | EHole | Case {callbacks = None;_} -> failwith "cannot evaluate holes"
  | Literal tbl -> tbl, funcs
  | Table x -> 
    let t_opt = String.Map.find valuation x  in 
    let t = t_opt |> Option.value_exn ~message:("Couldn't find table" ^ x) in 
    t, funcs
  | Map (exp, rexp) ->
    let tbl, funcs = e_eval funcs valuation exp in
    List.fold tbl ~init:([], funcs) ~f:(fun (acc_tbl, funcs) row -> 
      let new_rows, funcs = r_eval funcs rexp row in 
      acc_tbl @ new_rows, funcs
    )
  (* | Compose (e1, e2) -> 
    let tbl1, funcs = e_eval funcs valuation e1 in 
    let tbl2, funcs = e_eval funcs valuation e2 in 
    Value.compose tbl1 tbl2, funcs *)
  | Case {table; callbacks = Some callbacks} -> 
    let t, funcs = e_eval funcs valuation (Table table) in 
    let f funcs (ma : MatchAction.t) = 
      let action_name = Action.get_name ma.action in
      Printf.printf "Checking : %s in {%s}....." action_name
        (String.concat ~sep:" " @@ String.Map.keys callbacks)
      ;
      let callback = 
        String.Map.find callbacks action_name 
        |> Option.value_exn ~message:("Couldn't find " ^ action_name)
      in
      Printf.printf "yes!\n%!";
      r_eval funcs callback ma
    in
    List.fold t ~init:([], funcs) ~f:(fun (acc_tbl, funcs) row -> 
      let new_rows, funcs = f funcs row in 
      acc_tbl @ new_rows, funcs
    )

type t = 
  | Assign of { table: string; from : string list; body : exp }
  | Seq of t list

let rec hole_free = function 
  | Assign a -> exp_hole_free a.body
  | Seq cs -> List.for_all cs ~f:hole_free

let rec run' (funcs : skolems) (cfg : Config.t) : t -> Config.t * skolems = function 
  | Assign {table; from; body} -> 
    let cfg' = String.Map.filter_keys cfg ~f:(List.mem from ~equal:String.equal) in 
    let data, funcs = e_eval funcs cfg' body in 
    String.Map.set cfg ~key:table ~data, funcs
  | Seq cs ->
    List.fold cs ~init:(cfg, funcs) ~f:(fun (cfg, funcs) -> run' funcs cfg)

let run cfg prog = fst (run' String.Map.empty cfg prog)

let copy dst src = Assign {table = dst; from = [src]; body = Table src}

let const tbl key_types action args =
  Assign {table = tbl; from = [];
    body = Literal [
      MatchAction.{
        matches = String.Map.(map (of_alist_exn key_types) ~f:(fun w -> Match.Ternary (Trit.Vector.wc w)));
        action = Action.{name = action; args = String.Map.of_alist_exn args}
      }
    ]
  }

let case' tablename actions = 
  Case {
    table = tablename;
    callbacks = Some (String.Map.of_alist_exn actions)
  }

let renames mapping table =
  let callbacks_inner =
    List.map mapping ~f:(fun (old, new_) -> 
      (old, RenameActionTo new_)
      
  ) in 
  Case {table; callbacks = Some (String.Map.of_alist_exn callbacks_inner)}

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