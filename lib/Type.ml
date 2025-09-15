open Core

module ActionSet = Set.Make (Semantics.MagmaAction)

type varwidth = int [@@deriving sexp, compare]
type match_kind = Exact | LPM | Ternary | Range | Optional [@@deriving sexp, compare]
type table = {keys : varwidth String.Map.t;
              actions : ActionSet.t; 
              data : varwidth String.Map.t} [@@deriving sexp, compare]

type t = 
  | Table of table
  | Var of varwidth
  | Match of (varwidth * match_kind)
  [@@deriving sexp, compare]

type ctx = t String.Map.t


let mkeq mk mk' = 
  match mk, mk' with 
  | Exact, Exact 
  | LPM, LPM
  | Ternary, Ternary
  | Range, Range
  | Optional, Optional -> true
  | _,_ -> false

let castable original ~to_ = 
  (* this means "castable without incurring performance penalties" *)
  match original, to_ with 
  | Exact,_ 
  | LPM, LPM 
  | LPM, Ternary 
  | Range, Range
  | Optional, Optional 
  | Optional, Ternary 
  | Optional, LPM 
  | Optional, Range 
  | Ternary, Ternary -> true
  | _, _ -> false

let join mk1 mk2 = 
  match mk1, mk2 with
  | Exact, _ -> mk2
  | _, Exact -> mk1
  | LPM, LPM -> LPM
  | LPM, Ternary -> Ternary
  | Range, Range -> Range
  | Range, LPM | LPM, Range -> failwith "lpm and range incompatible matchkinds"
  | Range, Ternary | Ternary, Range -> failwith "range and ternary incompatible matchkinds"
  | Ternary, _ | _, Ternary -> Ternary
  | Optional, _ | _, Optional -> 
    failwith "Optional only compatible with Exact and Ternary, got something else"



let get_table = function 
  | Table t -> Some t
  | _ -> None

let get_table_exn typ = 
  get_table typ
  |> Option.value_exn ~message:"Type Error, expected table"


let get_actions ttype = ttype.actions

let get_action _ = failwith "No action?"

let get_action_exn typ =
  get_action typ
  |> Option.value_exn ~message:"Type Error: expected action"
  
let action_product (actions1 : ActionSet.t) (actions2 : ActionSet.t) : ActionSet.t = 
  let open Semantics.MagmaAction in 
  let actionslist1 = Set.to_list actions1 in 
  let actionslist2 = Set.to_list actions2 in
  List.fold actionslist1 ~init:ActionSet.empty ~f:(fun init a1 -> 
    List.fold actionslist2 ~init ~f:(fun acc a2 -> 
      Set.add acc (a1 @ a2)
    )
  )


let get_keys (t : table) : (string * int) list = 
  t.keys
  |> Map.to_alist

let get_data (t : table) : varwidth String.Map.t =
  t.data

let invert_table ( t : table ) : table = 
  {
    keys = get_data t |> String.Map.map ~f:(fun w -> w);
    actions = t.actions;
    data = t.keys
  }

let merge_keys_exn (skeys : int String.Map.t) (tkeys : int String.Map.t) : int String.Map.t = 
  Map.merge skeys tkeys ~f:(fun ~key -> function 
    | `Both (w, w') -> 
      if w = w' then 
        Some w
      else 
        failwithf "Type error on key %s, types differed when merging" key ()
    | `Left w | `Right w -> Some w
  )

let union_data_exn sdata tdata : varwidth String.Map.t =
  Map.merge sdata tdata ~f:(fun ~key -> function 
  | `Both (w, w') when w = w' -> 
    Some w
  | `Both _ -> failwithf "Type error on data %s: different widths when merging" key ()
  | `Left w | `Right w -> Some w
  )

let get_varwidth = function 
  | Var w -> Some w
  | _ -> None

let get_match_type = function 
  | Match m -> Some m
  | _ -> None


let get_varwidth_exn t =
  get_varwidth t
  |> Option.value_exn ~message:"Expected varwidth got something else"

let get_match_type_exn t =
  get_match_type t
  |> Option.value_exn ~message:"Expected match type got something else"

let find_exn (ctx : ctx) x =
  Map.find ctx x
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

let find_matchtype_exn ctx s = 
  find_exn ctx s 
  |> get_match_type_exn

let find_keys_exn (ctx : ctx) (name : string): (string * int) list =
  find_table_exn ctx name
  |> get_keys

let get_table_actions (ctx : ctx) t = (find_table_exn ctx t).actions

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
    Map.fold ctx ~init:[] ~f:(fun ~key ~data ctx -> 
        if f data then
            key :: ctx
        else 
            ctx
    )

let get_tables = get_names ~f:is_table
let get_all_actions = get_names ~f:is_action
let get_vars = Map.fold ~init:[] ~f:(fun ~key ~data vars -> 
    match data with 
    | Var w -> 
      (key, w)::vars
    | _ -> vars
  )

let get_vars_width w = get_names ~f:(is_var_width w)

let get_type_exn (ctx : ctx) name = Map.find_exn ctx name