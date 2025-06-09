open Core
let (let+) r f = Result.map r ~f


module Match = struct 
  type t = 
  | Exact of Bit.Vector.t
  | Lpm of Bit.Vector.t * int
  | Ternary of Trit.Vector.t

  let catch_all width = Ternary (Trit.Vector.wc width)

  let equal m m' = 
    match (m, m') with 
    | Exact x, Exact y -> 
      Bit.Vector.equal x y
    | Lpm (x, w), Lpm (y,l) -> Bit.Vector.equal x y && w = l
    | Ternary v, Ternary v' ->
      Trit.Vector.equal v v' 
    | Ternary v, Exact v' | Exact v', Ternary v -> 
      let tv' = Trit.Vector.of_bv v' in 
      Trit.Vector.equal v tv'
    | _, _ -> false

  let matches x = function
    | Exact y -> Bit.Vector.equal x y
    | Lpm _ -> failwith "TODO implement lpm"
    | Ternary v -> Trit.Vector.mem x v

  let to_string = function 
    | Exact v -> Bit.Vector.to_string v
    | Lpm (v, bits) -> Printf.sprintf "%s/%d" (Bit.Vector.to_string v) bits
    | Ternary tv -> Printf.sprintf "%s" (Trit.Vector.to_string tv)

  let get_exact = function 
    | Exact v -> v
    | Lpm _ -> failwith "Expected Exact; got LPM"
    | Ternary _ -> failwith "Expected Exact; got Ternary"

  let to_exact = function 
  | Exact v  -> Exact v
  | Lpm (bv, w) when Bit.Vector.length bv = w -> 
    Exact bv
  | Lpm _ -> failwith "cannot get exact from inexact LPM"
  | Ternary tv -> 
    Exact (Trit.Vector.to_bv_exn tv)

  let get_tv = function 
    | Exact v -> Trit.Vector.of_bv v
    | Lpm _ -> failwith "TODO: LPM -> TV"
    | Ternary tv -> tv

  let incr = function 
    | Exact v -> [Exact Bit.Vector.(incr v)]
    | Lpm (v, w) -> 
        let v' = Trit.Vector.(of_bv v |> drop_last_n w) in
        let tv = Trit.Vector.(v' @ wc w) in 
        failwithf "TODO: Increment %s" (Trit.Vector.to_string tv) ()
    | Ternary tv when Trit.Vector.all_wild tv -> 
      [Ternary tv]
    | Ternary tv -> 
      Intify.realize_operation "x" tv (Intify.Exp.xincr "x")
      |> List.map ~f:(fun tv -> Ternary tv)

  let decr = function 
    | Exact v -> [Exact Bit.Vector.(decr v)]
    | Lpm _ -> failwith "Cannot decrement LPM"
    | Ternary tv -> 
      Intify.realize_operation "x" tv (Intify.Exp.xdecr "x")
      |> List.map ~f:(fun tv -> Ternary tv)
end


module Action = struct
  type t = {
    name : string;
    args : Bit.Vector.t String.Map.t
  }

  let equal (a : t) (b : t) =
    String.(a.name = b.name) &&
    String.Map.equal Bit.Vector.equal a.args b.args

  let to_string ({name;args} : t) : string =
    let open Printf in 
    String.Map.fold args ~init:"" ~f:(fun ~key ~data acc -> 
      let argstr = sprintf "%s = %s" key (Bit.Vector.to_string data) in 
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

  let get_data_exn (action : t) (name : string) =
    get_data action name
    |> Option.value_exn ~message:(Printf.sprintf "Couldnt find action data param %s" name)

  let get_data' = Fun.flip get_data

  let get_data_exn' = Fun.flip get_data_exn

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
  let to_string ({matches; action}: t) = 
    Printf.sprintf "\t%s -> %s" 
      (String.Map.to_alist matches |> List.map ~f:(fun (x,m) -> Printf.sprintf "'%s' ~ %s" x (Match.to_string m)) |> String.concat ~sep:", ")
      (Action.to_string action)

  let equal (ma : t) (ma' : t) =
    String.Map.equal Match.equal ma.matches ma'.matches 
    && Action.equal ma.action ma'.action

  let get_match (ma : t) name = 
    String.Map.find_exn ma.matches name

  let get_field (ma : t) name =
    match Action.get_data ma.action name with 
    | None -> get_match ma name
    | Some v -> Match.Exact v

  let does_match keys ({matches;action=_} : t) =
    String.Map.for_alli matches ~f:(fun ~key:x ~data:mtch -> 
      match String.Map.find keys x with 
      | None -> false
      | Some value -> 
        Match.matches value mtch
    )

  let runs_action name (ma : t) = Action.has_name ma.action name

  let restrict_keys ma keys = 
    {ma with 
      matches = String.Map.filter_keys ma.matches ~f:(String.(List.mem keys ~equal))
    }
    
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

  let bind ~f : t -> t =
    List.bind ~f

  let size (mat : t) =
    List.length mat

  end
