open Core

type varwidth = int
type match_kind = Exact | LPM | Ternary | Range | Optional
type table = {keys : (varwidth * match_kind) String.Map.t;
              actions : string list; 
              data : varwidth String.Map.t}

type t = 
  | Table of table
  | Var of varwidth
  | Match of (varwidth * match_kind)

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
  (* this is "castable without incurring performance penalties" *)
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


let get_table = function 
  | Table t -> Some t
  | _ -> None

let get_table_exn typ = 
  get_table typ
  |> Option.value_exn ~message:"Type Error, expected table"

let get_action _ = failwith "No action?"

let get_action_exn typ =
  get_action typ
  |> Option.value_exn ~message:"Type Error: expected action"
  

let get_keys (t : table) : (string * int) list = 
  t.keys
  |> String.Map.map ~f:fst
  |> String.Map.to_alist

let get_data (t : table) : varwidth String.Map.t =
  t.data

let invert_table ( t : table ) : table = 
  {
    keys = get_data t |> String.Map.map ~f:(fun w -> (w, Exact));
    actions = t.actions;
    data = String.Map.map t.keys ~f:fst
  }

let merge_keys_exn (skeys : (int * match_kind) String.Map.t) (tkeys : (int * match_kind) String.Map.t) : (varwidth * match_kind) String.Map.t = 
  String.Map.merge skeys tkeys ~f:(fun ~key -> function 
    | `Both ((w, mk), (w',mk')) -> 
      if w = w' && mkeq mk mk' then 
        Some (w, mk)
      else 
        failwithf "Type error on key %s, types differed when merging" key ()
    | `Left (w,mk) | `Right (w,mk) -> Some (w,mk)
  )

let union_data_exn sdata tdata : varwidth String.Map.t =
  String.Map.merge sdata tdata ~f:(fun ~key -> function 
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