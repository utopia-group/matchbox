open Core
let (let+) r f = Result.map r ~f


module Match = struct 
  type t = 
  | Exact of int
  | Lpm of int * int
  | Ternary of int * int
  | Optional of int option

  let equal m m' = 
    match (m, m') with 
    | Exact x, Exact y -> x = y
    | Lpm (x, w), Lpm (y,l) -> x = y && w = l
    | Ternary (x,m), Ternary (y, m') -> x = y && m = m'
    | Optional o, Optional o' -> Option.equal Int.equal o o'
    | _, _ -> false

  let matches x = function
    | Exact y -> x = y
    | Lpm _ -> failwith "TODO implement lpm"
    | Optional None -> true
    | Optional (Some y) -> x = y 
    | Ternary (y, mask) -> (y land mask) = (x land mask)

  let to_string = function 
    | Exact v -> Int.to_string v
    | Lpm (v, bits) -> Printf.sprintf "%d/%d" v bits
    | Ternary (v, m) -> Printf.sprintf "%d & %d" v m
    | Optional None -> "*"
    | Optional (Some v) -> Int.to_string v

  let get_exact = function 
    | Exact v -> v
    | Lpm _ -> failwith "Expected Exact; got LPM"
    | Ternary _ -> failwith "Expected Exact; got Ternary"
    | Optional _ -> failwith "Expected Exact; got optional"

  let incr = function 
    | Exact v -> Exact (v + 1)
    | Lpm _ -> failwith "cannot increment LPM"
    | Ternary _ -> failwith "cannot increment ternary"
    | Optional (Some v) -> Optional (Some (v + 1))
    | Optional None -> Optional None

  let decr = function 
    | Exact v -> Exact (v - 1)
    | Lpm _ -> failwith "Cannot decrement LPM"
    | Ternary _ -> failwith "cannot decrement ternary"
    | Optional (Some v) -> Optional (Some (v - 1))
    | Optional (None) -> Optional None
end


module Action = struct
  type t = {
    name : string;
    args : int String.Map.t
  }

  let equal (a : t) (b : t) =
    String.(a.name = b.name) &&
    String.Map.equal Int.equal a.args b.args

  let to_string ({name;args} : t) : string =
    let open Printf in 
    String.Map.fold args ~init:"" ~f:(fun ~key ~data acc -> 
      let argstr = sprintf "%s = %d" key data in 
      if String.length acc = 0 then 
        argstr
      else 
        sprintf "%s, %s" acc argstr
    )
    |> sprintf "%s(%s)" name


  let get_name action = action.name
  let has_name (action : t) name = 
    String.(action.name = name)
  let set_name name action =
    {action with name}

  let has_data (action : t) = String.Map.mem action.args

  let get_data (action : t) (name : string) = 
    String.Map.find action.args name
    |> Option.value_exn ~message:(Printf.sprintf "Couldnt find action data param %s" name)

  let get_data' = Fun.flip get_data

  let project_data (params : string list) (action : t) = 
    {action with args =
      String.Map.filter_keys action.args ~f:String.(List.mem params ~equal)}

  let update_data action b v =
    { action with args = 
      String.Map.set action.args ~key:b ~data:v
    }
end

module MatchAction = struct 
  type t = {
    matches : Match.t String.Map.t;
    action : Action.t;
  }

  let equal (ma : t) (ma' : t) =
    String.Map.equal Match.equal ma.matches ma'.matches 
    && Action.equal ma.action ma'.action 

  let to_string ({matches; action}: t) = 
    Printf.sprintf "\t%s  ->  %s" 
      (String.Map.to_alist matches |> List.map ~f:(fun (x,m) -> x ^ " ~ " ^ Match.to_string m) |> String.concat ~sep:", ")
      (Action.to_string action)


  let get_match (ma : t) name = 
    String.Map.find_exn ma.matches name

  let does_match keys ({matches;action=_} : t) =
    String.Map.for_alli matches ~f:(fun ~key:x ~data:mtch -> 
      match String.Map.find keys x with 
      | None -> false
      | Some value -> 
        Match.matches value mtch
    )

  let runs_action name (ma : t) = Action.has_name ma.action name
    
end

module MatchActionTable = struct 
  type t = MatchAction.t list

  let equal = List.equal MatchAction.equal

  let to_string mas = 
    mas
    |> List.map ~f:MatchAction.to_string
    |> String.concat ~sep:"\n"

  let find_match (entries : t) keys = 
    List.find entries ~f:(MatchAction.does_match keys)
    |> Option.value_exn ~message:"Couldnt find any matching rows in table"

  let run (entries : t) keys = 
    let entry = find_match entries keys in 
    entry.action

  let get_matches name entries = 
    List.map entries ~f:(Fun.flip MatchAction.get_match name)

  let get_actions (name: string) entries = 
    List.filter entries ~f:(MatchAction.runs_action name)
    |> List.map ~f:(fun (ma : MatchAction.t) -> ma.action)

  let map ~f : t -> t= 
    List.map ~f

  end
