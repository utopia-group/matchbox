open Core


type varwidth = int
type table = {keys : string list; actions : string list}
type action = string list

type t = 
  | Table of table
  | Action of action
  | Var of varwidth

type ctx = t String.Map.t


let get_table = function 
  | Table t -> Some t
  | _ -> None

let get_table_exn typ = 
  get_table typ
  |> Option.value_exn ~message:"Type Error, expected table"

let get_action = function 
  | Action a -> Some a
  | _ -> None

let get_action_exn typ =
  get_action typ
  |> Option.value_exn ~message:"Type Error: expected action"
  

let get_varwidth = function 
  | Var w -> Some w
  | _ -> None

let get_varwidth_exn t =
  get_varwidth t
  |> Option.value_exn ~message:"Expected varwidth got something else"


let find_exn (ctx : ctx) x =
  String.Map.find ctx x
  |> Option.value_exn ~message:("Could not find " ^ x ^ " in type context")

let find_table_exn (ctx : ctx) t = 
  find_exn ctx t
  |> get_table_exn

let find_action_exn ctx t = 
  find_exn ctx t
  |> get_action_exn 

let find_varwidth_exn ctx t =
  find_exn ctx t 
  |> get_varwidth_exn

let get_keys (ctx : ctx) t =
  (find_table_exn ctx t).keys
  |> List.map ~f:(fun k -> 
    k, find_varwidth_exn ctx k
  )

let get_table_actions (ctx : ctx) t = (find_table_exn ctx t).keys

let is_table typ = 
  get_table typ 
  |> Option.is_some
let is_var typ = 
  get_varwidth typ
  |> Option.is_some

let is_action typ = 
  get_action typ
  |> Option.is_some

let is_var_width w typ = 
    get_varwidth typ 
    |> Option.value_map ~f:((=) w) ~default:false

let get_names ~f (ctx : ctx) = 
    String.Map.fold ctx ~init:[] ~f:(fun ~key ~data ctx -> 
        if f data then
            key :: ctx
        else 
            ctx
    )

let get_tables = get_names ~f:is_table
let get_all_actions = get_names ~f:is_action
let get_vars = String.Map.fold ~init:[] ~f:(fun ~key ~data vars -> 
    match data with 
    | Var w -> 
      (key, w)::vars
    | _ -> vars
  )

let get_vars_width w = get_names ~f:(is_var_width w)

let get_type_exn (ctx : ctx) name = String.Map.find_exn ctx name