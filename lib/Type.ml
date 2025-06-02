open Core

type table = {keys : string list; actions : string list}
type action = string list
type varwidth = int

type t = 
  | Table of table
  | Action of action
  | Var of varwidth

type ctx = t String.Map.t

let get_table = function 
  | Table t -> Some t
  | _ -> None

let get_action = function 
  | Action a -> Some a
  | _ -> None

let get_varwidth = function 
  | Var w -> Some w
  | _ -> None

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
let get_actions = get_names ~f:is_action
let get_vars = get_names ~f:is_var
let get_vars_width w = get_names ~f:(is_var_width w)

let get_type_exn (ctx : ctx) name = String.Map.find_exn ctx name