(** A SYNTHESIS DSL for expressing table queries *)
open Core

let commute = Result.all

let (<$>) f xs = List.map xs ~f
let (=<<) f xs = List.bind xs ~f
let (<*>) fs xs = 
  let open List in 
  fs >>= fun f -> 
  xs >>| fun x -> 
  f x

let (>>=) r f = Result.bind r ~f
let (let*) = (>>=)
let (let**) r f = (commute r) >>= f
let (>>|) r f = Result.map r ~f
let (let+) = (>>|)
let (let++) r f = (commute r) >>| f

let (>>=*) (l : 'a list) (f : 'a -> ('b list, 'c) result) : ('b list, 'c) result = 
  List.map l ~f |> commute >>| List.concat


let ($>>=$) (res: (('a * 'b) list, string) result) (f : ('a * 'b) -> ('c list, string) result) = 
  let* svs = res in
  svs >>=* f

let (let*$) = ($>>=$)


let uncurry f (x, y) = f x y

let res_acc_bind xs init f = 
  List.fold xs ~init:(Ok (init, [])) ~f:(fun result x -> 
    let* (acc, ys) = result in
    let+ acc', y = f acc x in
    acc', ys @ y
  )

let res_acc_map xs init f = 
  List.fold xs ~init:(Ok (init, [])) ~f:(fun result x -> 
    let* (acc, ys) = result in
    let+ acc', y = f acc x in
    acc', ys @ [y]
  )

module ExprType = struct
  type t = int
end

module ActionType = struct
  type t = ExprType.t String.Map.t

  let get_param_type a param = 
    String.Map.find a param
    |> Option.value_exn ~message:(Printf.sprintf "could not find param %s in action" param)

end

module TableType = struct  
  type t = {
    input_types : ExprType.t String.Map.t;
    actions : ActionType.t String.Map.t;
  }

  let get_key (typ : t) name = 
    String.Map.find typ.input_types name
    |> Option.value_exn ~message:(Printf.sprintf "TypeError %s is not a defined key" name)

  let get_action (typ : t) name = 
    String.Map.find typ.actions name 
    |> Option.value_exn ~message:(Printf.sprintf "Couldnt find action %s" name)
end


module Type = struct 
  type t = 
    | Table of TableType.t
    | Expr of ExprType.t
    | Action of ActionType.t

  let type_type = function
    | Table _ -> "Table"
    | Expr _ -> "Expr"
    | Action _ -> "Action"

  let type_error exp got = 
    failwith (Printf.sprintf "TypeError. Expected %s, got %s" exp (type_type got))

  let get_table t = 
    match t with 
    | Table tbl -> tbl
    | _ -> type_error "Table" t
  
  let get_expr t = 
    match t with
    | Expr e -> e
    | _ -> type_error "Expr" t

  let get_action t = 
    match t with 
    | Action a -> a
    | _ -> type_error "Action" t

  let get_table_action t action = 
    let tbl = get_table t in 
    TableType.get_action tbl action

  let get_action_data a param = 
    let a = get_action a in 
    ActionType.get_param_type a param

  let get_table_key t idx = 
    let tbl = get_table t in 
    TableType.get_key tbl idx

    
end

module TypeContext = struct
  type t = Type.t String.Map.t

  let find gamma name = 
    String.Map.find gamma name
    |> Option.value_exn ~message:(Printf.sprintf "TypeError: Couldn't find %s in type context" name)
end
module TableExpression = struct
  type halgo =
  | SHA of int
  | CRC of int

  type ftype =
  | Incr
  | Hash of halgo

  type t = 
  | Table of string
  | Key of (t * string)
  | Action of (t * string)
  | Data of (t * string)
  | LiteralAction of (string * t String.Map.t)
  | LiteralName of string
  | Name of t
  | Rename of (t * string)
  | Project of (t * string list)
  | Union of (t * t)
  | Function of (string * t list * Type.t * ftype)

  let rec typecheck (gamma : TypeContext.t) e : Type.t =
    match e with 
    | Table name -> 
      let t = TypeContext.find gamma name in
      let tt = Type.get_table t in 
      Type.Table tt
    | Key (e, idx) ->
      let t = typecheck gamma e in 
      let w = Type.get_table_key t idx in 
      Type.Expr w
    | Action (e, name) -> 
      let t = typecheck gamma e in 
      let a = Type.get_table_action t name in 
      Type.Action a
    | Data (e, name) -> 
      let t = typecheck gamma e in 
      let w = Type.get_action_data t name in 
      Type.Expr w
    | _ -> failwith "TODO typechecking"
end

module Config = struct
  open Semantics
  
  type t = MatchActionTable.t String.Map.t

  let equal = 
    String.Map.equal MatchActionTable.equal
  let to_string (cfg : t) = 
    String.Map.fold cfg ~init:None ~f:(fun ~key ~data acc -> 
      Printf.sprintf "%stable %s\n%s\n\n" 
        (Option.value acc ~default:"")
        key
        (MatchActionTable.to_string data)
      |> Option.some
    )
    |> Option.value_exn

  let find (cfg : t) (name : string) = 
    String.Map.find cfg name 
    |> Option.value_exn ~message:(Printf.sprintf "Couldn't find %s in table configuration" name)

  let set (cfg : t) (name : string) (entries) = 
    String.Map.set cfg ~key:name ~data:entries

  let refine (cfg : t) (names : string list) = 
    if List.for_all names ~f:(String.Map.mem cfg) then
      String.Map.filter_keys cfg
        ~f:String.(List.mem names ~equal)
    else
      failwith "Couldn't refine config, missing names"

  let ( <~ ) cfg updates = 
    List.fold updates ~init:cfg ~f:(fun cfg (name, entries) -> 
      set cfg name entries)
  let ( |=> ) name entries = (name, entries)
end

module State : sig
  open Semantics
  type t 
  val empty : t
  val fresh : t -> string -> Match.t list -> t * int
  val equal : t -> t -> bool
end = struct 
  open Semantics
  type t = (Match.t list list) String.Map.t 
  let empty : t = String.Map.empty

  let equal : t -> t -> bool = String.Map.equal (List.equal (List.equal Match.equal))
  let empty_incr_state = []

  let find (state : t) (func : string) = 
    match String.Map.find state func with 
    | None -> empty_incr_state
    | Some incr -> incr

  let fresh (state : t) (func : string) (inputs : Match.t list)  : t * int = 
    let seen = find state func in
    match List.findi seen ~f:(fun _ -> List.equal Match.equal inputs) with
    | None -> 
      let incr_state = seen @ [inputs] in
      String.Map.set state ~key:func ~data:incr_state,
      List.length seen
    | Some (idx,_) -> 
      state,
      idx
end

    


module Value = struct 
  module E = TableExpression
  open Semantics
  type t = 
    | T of MatchActionTable.t
    | V of Match.t
    | A of Action.t
    | R of (Match.t List.t * Action.t)
    | N of string
    | B of bool

  let to_string = function 
  | T mat -> MatchActionTable.to_string mat
  | V m -> Match.to_string m
  | A a -> Action.to_string a
  | N name -> name
  | B true -> "true"
  | B false -> "false"
  | R (ms, a) -> List.to_string ~f:Match.to_string ms ^ " |-> " ^ Action.to_string a

  let equal v1 v2 =
    match v1, v2 with 
    | T mat, T mat' -> 
      MatchActionTable.equal mat mat'
    | V m, V m' -> 
      Match.equal m m'
    | A a , A a' -> 
      Action.equal a a'
    | N name, N name' -> 
      String.equal name name'
    | B b, B b' -> Bool.(b = b')
    | R (ms,a), R(ms',a') -> List.equal Match.equal ms ms' && Action.equal a a'
    | _, _ -> false

  let t t = T t
  let ts = List.map ~f:t
  let v v = V v
  let bv v = V (Exact v)
  let vs = List.map ~f:v
  let a a = A a
  let as_ = List.map ~f:a
  let n n = N n 
  let ns n = List.map ~f:n
  let b b = B b
  let bs b = List.map ~f:b
  let r ma = R ma
  let rs = List.map ~f:r

  let get_table = function 
    | T ma -> ma
    | v -> failwithf "expected table, got %s" (to_string v) ()

    let get_action = function 
    | A a -> a 
    | v -> failwithf "expected action, got %s" (to_string v) ()
    
    
  let get_name = function 
    | N n -> n
    | v -> failwithf "expected name, got %s" (to_string v) ()

  let get_vectorset = function 
    | V v -> v
    | v -> failwithf "expected vectorset, got %s" (to_string v) ()

  let get_1vector value = 
    let v = get_vectorset value in 
    Match.get_exact v

  let truthy = function 
  | B b -> b
  | v -> failwithf "expected bool, got %s" (to_string v) ()

  let get_row = function 
    | R ma -> ma
    | v -> failwithf "expected row, got %s" (to_string v) ()

  let return state f xs = 
    List.map xs ~f:(fun x -> 
      (state, f x)
    )

  let rec eval (state : State.t) (cfg : Config.t) (e : E.t) = 
    match e with 
    | Table name ->
      let t = Config.find cfg name in 
      Ok (state, List.return (T t))
    | Key (exp, idx) ->
      let+ state, vlus = eval state cfg exp in
      let tbls = get_table <$> vlus in 
      let matches = List.(tbls >>= MatchActionTable.get_matches idx) in 
      (state, v <$> matches)
    | Action (exp, name) -> 
      let+ state, vlus = eval state cfg exp in 
      let tbls = get_table <$> vlus in 
      let acts = MatchActionTable.get_actions name =<< tbls in 
      (state, a <$> acts)
    | Data (exp, name) ->
      let+ state, vlus = eval state cfg exp in 
      let acts = get_action <$> vlus in 
      let data = Action.get_data_exn' name <$> acts in
      (state, bv <$> data)
    | LiteralAction(name, arg_exprs) -> 
      let+ state, argss = 
        String.Map.fold arg_exprs ~init:(Ok (state, [String.Map.empty]))
        ~f:(fun ~key ~data res -> 
          let* state, args_so_far = res in  
          let+ state, values = eval state cfg data in 
          let vectors = get_1vector <$> values in 
          let update d = String.Map.set ~key ~data:d in 
          (state, update <$> vectors <*> args_so_far)
        )
      in
      let actionify args = Action.{name; args} in 
      (state, a <$> (actionify <$> argss))
    | Name exp -> 
      let+ state, vlus = eval state cfg exp in 
      let actions = get_action <$> vlus in 
      (state, n <$> (Action.get_name <$> actions))
    | Rename (exp, newname) -> 
      let+ state, values = eval state cfg exp in 
      let actions = get_action <$> values in 
      (state, a <$> (Action.set_name newname <$> actions))
    | Project (exp, params) -> 
      let+ state, vlus = eval state cfg exp in 
      let actions = get_action <$> vlus in 
      (state, a <$> (Action.project_data params <$> actions))
    | LiteralName name -> 
      Ok (state, [n name])
    | Union (e1, e2) -> 
      let* state, vs1 = eval state cfg e1 in 
      let+ state, vs2 = eval state cfg e2 in 
      state, vs1 @ vs2
    | Function (name, inputs, typ, halgo) -> 
      begin match halgo, typ with 
      | Incr, Expr width -> begin
        let lookup state in_values : (State.t * t, string) result = 
          let in_ints = get_vectorset <$> in_values in
          let (state, out) = State.fresh state name in_ints in 
          Ok (state, v (Exact Bit.Vector.(of_int ~width out)))
        in
        let* state, in_values_alternatives = 
          res_acc_map inputs state (fun state inp -> eval state cfg inp)
        in 
        let+ state, vs = 
          res_acc_map in_values_alternatives state lookup
        in 
        state, vs
      end
      | Incr, _ -> 
        failwith "Incr function algo expects Expr type"
      | Hash _, _ -> failwith "TODO hashing"
      end
end

module TableFormula = struct 
  module TE = TableExpression
  type t = 
  | True 
  | False 
  | Eq of TE.t * TE.t
  | And of t * t

  let rec eval state cfg (phi : t) = 
    match phi with 
    | True -> Ok (state, true)
    | False -> Ok (state, false)
    | Eq (e1, e2) -> 
      let* state, vs1 = Value.eval state cfg e1 in 
      let+ state, vs2 = Value.eval state cfg e2 in 
      state, List.equal Value.equal vs1 vs2
    | And (phi1, phi2) -> 
      let* state, b1 = eval state cfg phi1 in 
      if b1 then
        eval state cfg phi2
      else 
        Ok (state, false)
end

module TableMapping = struct
  module MA = Semantics.MatchAction
  module TE = TableExpression
  module TF = TableFormula
  type t = 
    | Assign of {
      table : string;
      keys : TE.t list;
      action : TE.t;
      from : string list;
    }
    | Seq of t list
    | If of TF.t * t * t

  let andthen ms = Seq ms

  let rec rfold ~init ~f xs = 
    match xs with 
    | [] -> Ok init
    | x::xs -> 
      match f init x with 
      | Error msg -> Error msg
      | Ok init -> 
        rfold xs ~init ~f

  let mk_ma (vmatches, vaction) =
    let matches = String.Map.map vmatches ~f:(Value.get_vectorset) in
    let action = Value.get_action vaction in 
    MA.{matches;action}

  let rec eval (state, cfg) (mapping : t)  : (State.t * Config.t, string) result =
    match mapping with 
    | Seq cs -> 
      rfold cs ~init:(state, cfg) ~f:eval
    | Assign {table=_;keys=_;action=_;from=_} ->
      failwith "ill-defined"
      (* let cfg' = Config.refine cfg from in
      let* state, rows_matches = res_acc_map keys state (fun state key -> Value.eval state cfg' key)  in 
      let matches_rows = List.transpose_exn rows_matches in 
      let+ state, actions = Value.eval state cfg' action in
      List.iteri matches_rows ~f:(fun i ms -> 
        Printf.printf "\t match: %d %s\n%!" i (List.to_string ~f:(Value.to_string) ms));

      let entries = mk_ma <$> List.zip_exn matches_rows actions in
      state, Config.(cfg <~ [table |=> entries]) *)
    | If (phi, tru, fls) -> 
      let* state, cond = TF.eval state cfg phi in 
      if cond then 
        eval (state, cfg) tru
      else 
        eval (state, cfg) fls
  
end

