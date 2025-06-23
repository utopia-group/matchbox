open Core
open DSLv2

let restrict strings = List.filter ~f:(fun (key, _) -> String.(List.mem strings key ~equal))

let alist_find_exn x map = 
  match List.filter map ~f:(fun (y,_) -> String.(x = y)) with 
  | [(_,exp)] -> exp
  | [] -> failwithf "couldn't find %s in association list, but I expected it" x ()
  | _ -> failwithf "found multiple entries for %s in association list, which violates the invariant" x ()

let alist_set m key data =
  List.map m ~f:(fun (x, e) -> 
    if String.(x = key) then 
      (x, data)
    else 
      (x, e)
  )


module SymbolicMatch = struct 
  type t = (string * SMT.expr) list

  let restrict = restrict

  let get_map (m : t) : SMT.expr String.Map.t = 
    String.Map.of_alist_exn m

  let set = alist_set

  let of_table (gamma : Type.ctx) (tbl : string) : t =
    (Type.find_table_exn gamma tbl).keys
    |> List.map ~f:(fun key -> 
      (key, SMT.var key)
    )
  
  let to_smt : t -> SMT.expr list = List.map ~f:snd
end

module SymbolicAction = struct
  type args = (string * SMT.expr) list
  type t = (string * args) list

  let rename aname (symb : t) =
    List.map symb ~f:(fun (_, args) -> (aname, args))
    

  let slice vars symb =
    List.map symb ~f:(fun (aname, args) -> 
      (aname, restrict vars args)
    )

  let get_map _ = failwith "IDK HOW TO DO THIS"

  let set_arg act key data =
    List.map act ~f:(fun (name, args) ->
      (name, alist_set args key data)
    )

  let of_table (gamma : Type.ctx) (tbl : string) : t =
    let Type.{actions;_} = Type.find_table_exn gamma tbl in 
    List.map actions ~f:(fun name -> 
      let params = Type.find_action_exn gamma name in 
      let args = List.map params ~f:(fun x -> 
        (x, SMT.var x)
      )
      in
      (name,args)
    )

  let to_smt (act : SMT.expr) (symb:t) : SMT.expr =
    List.map symb ~f:(fun (aname, args) -> 
      let action = 
        List.map args ~f:snd
        |> SMT.symb (String.capitalize aname) 
      in 
      SMT.((=) [act; action])
    )
    |> SMT.or_

end

let context (m : SymbolicMatch.t) (a : SymbolicAction.t) =
  m @ List.concat_map a ~f:(fun (_, args) -> args)

let rec exp_compile (ctx : (string * SMT.expr) list) (e : bvexp) =
  match e with 
  | BVHole -> failwith "Cannot Translate Hole"
  | Var (x,_) -> 
    alist_find_exn x ctx
  | Lit bv -> 
    SMT.bv' bv
  | Fun _ -> failwith "not sure how to translate functions"
  | Incr e' -> 
    let smtexp' = exp_compile ctx e' in
    let width = bvexp_width e' in
    let one =  Bit.Vector.one width in 
    SMT.((+) [smtexp'; bv' one])
  | Decr e' -> 
    let smtexp' = exp_compile ctx e' in 
    let width =  bvexp_width e' in 
    let one = Bit.Vector.one width in 
    SMT.((-) [smtexp'; bv' one])

let rec row_interp (r : rowexp) m a =
  match r with 
  | Id -> (m, a)
  | RHole -> failwith "Cannot compile a hole"
  | RenameActionTo a' -> 
    (m, SymbolicAction.rename a' a)
  | MapKey(out, args, e) ->
    let ctx = context m a |> restrict args in 
    let symbe = exp_compile ctx e in 
    let m = SymbolicMatch.set m out symbe in 
    (m, a)
  | MapData(out, args, e) -> 
    let ctx = context m a |> restrict args in 
    let symbe = exp_compile ctx e in 
    let a = SymbolicAction.set_arg a out symbe in 
    (m, a)
  | Pipe(r1, r2) -> 
    let m1, a1 = row_interp r1 m a in 
    row_interp r2 m1 a1
  | DataSlice data -> 
    (m, SymbolicAction.slice data a)
  | KeySlice keys -> 
    (SymbolicMatch.restrict keys m, a)

let table t m =
  SymbolicMatch.to_smt m
  |> SMT.symb t

let table_exp_interp ctx (t : string) (body : exp) =
  match body with 
  | EHole -> failwith "Cannot Interpret Hole"
  | Literal _ -> failwith "literal"
  | Compose _ -> failwith "compositions not allowed, must be normalized first"
  | Table s -> 
    let ms = SymbolicMatch.of_table ctx t in
    SMT.((=) [
      (table t ms);
      (table s ms);
    ])
  | Map (Table s, r) ->
    let m = SymbolicMatch.of_table ctx s in
    let a = SymbolicAction.of_table ctx s in
    let sact = SMT.var (s ^ "$action") in
    let tact = SMT.var (t ^ "$action") in
    let m', a' = row_interp r m a in 
    SMT.(implies [
      SymbolicAction.to_smt sact a;
      SymbolicAction.to_smt tact a';
      iff [(=) [table s m; sact];
           (=) [table t m'; tact]]
    ])
  | Map (_ , _) -> failwith "can only map over literal tables, please normalize"
  | Case _ -> failwith "TODO"

let rec compile types (prog : DSLv2.t) =
  match prog with 
  | Assign asgn -> 
    table_exp_interp types asgn.table asgn.body
  | Seq cs -> 
    SMT.(and_ (List.map cs ~f:(compile types)))

module Fresh = struct 
  type t = int String.Map.t

  let empty : t = String.Map.empty

  let en ctx x =
    let i = String.Map.find ctx x |> Option.value ~default:0 in
      String.Map.set ctx ~key:x ~data:(i+1),
      Printf.sprintf "x$%d" i

end

let rec lift_body (ctx : Fresh.t) (table : string) (body : exp) =
  match body with 
  | EHole | Literal _ | Table _ | Map(Table _, _) | Case{table=Table _; _}-> 
    let ctx, table = Fresh.en ctx table in 
    ctx, table, [table, body]
  | Compose (e1, e2) -> 
    let ctx, _,  pairs1 = lift_body ctx table e1 in 
    let ctx, table', pairs2 = lift_body ctx table e2 in 
    ctx, table', pairs1 @ pairs2
  | Map (exp, rexp) -> 
    let ctx, table', pairs = lift_body ctx table exp in 
    let ctx, table'' = Fresh.en ctx table in 
    ctx, table'', pairs @ [table'', Map (Table table', rexp)]
  | Case {table=table_exp; callbacks} -> 
    let ctx, table', pairs = lift_body ctx table table_exp in 
    let ctx, table'' = Fresh.en ctx table in 
    ctx, table'', pairs @ [table', Case {table = Table table'; callbacks}]

let rec lift (ctx : Fresh.t) = 
  function
  | Assign {table;from;body} ->
    let ctx, _, assigns = lift_body ctx table body in 
    let cs' = List.map assigns ~f:(fun (table, body) -> Assign {table; from; body} ) in 
    ctx, Seq cs'
  | Seq cs -> 
    let ctx, cs' = List.fold cs ~init:(ctx, Seq []) ~f:(fun (ctx, cs') c -> 
      let ctx, cs = lift ctx c in 
      (ctx, Seq[cs'; cs])
    ) in
    ctx, cs'

let tbl_actions_name name =
  Printf.sprintf "%sAction" (String.capitalize name)

let compile types matchstix =
  let _, normalized = lift (Fresh.empty) matchstix in
  compile types normalized
