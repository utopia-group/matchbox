open Core
let (let+) r f = Result.map r ~f


module Match = struct 
  type t = 
  | Exact of Bit.Vector.t
  | Lpm of Bit.Vector.t * int
  | Ternary of Trit.Vector.t
  [@@deriving sexp, compare]

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

  let to_mask_pair m = get_tv m |> Trit.Vector.to_bitmask

  let length = function 
    | Exact (v) | Lpm (v, _) -> 
      Bit.Vector.length v
    | Ternary v -> 
      Trit.Vector.length v

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

  let remask mask = function 
  | Ternary tv -> 
    let bv, _ = Trit.Vector.to_bitmask tv in 
    Ternary (Trit.Vector.of_bitmask bv mask)
  | Exact v | Lpm (v,_) -> 
    Ternary (Trit.Vector.of_bitmask v mask)

  let exact bv = Exact bv

  let unsafe_explicit_set = function 
    | Exact bv -> [bv]
    | Lpm _ -> failwith "TODO enumerate LPM "
    | Ternary _ -> failwith "TODO enumerate TV"

  let intersect m1 m2 =
    let tv1 = get_tv m1 in 
    let tv2 = get_tv m2 in 
    match Trit.Vector.intersect tv1 tv2 with 
    | None -> None 
    | Some tv -> Some (Ternary tv)

  let empty_intersection m1 m2 = intersect m1 m2 |> Option.is_none

  let get_type = function
    | Exact bv -> (Bit.Vector.length bv, Type.Exact)
    | Lpm (bv, _) -> (Bit.Vector.length bv, Type.LPM)
    | Ternary tv -> (Trit.Vector.length tv, Type.Ternary)

end


module Action = struct
  type t = {
    name : string;
    args : Bit.Vector.t String.Map.t
  }

  let make name args : t = {name; args}

  let compare a1 a2 = 
    Tuple2.compare (a1.name, a1.args) (a2.name, a2.args) 
      ~cmp1:String.compare
      ~cmp2:(String.Map.compare Bit.Vector.compare)


  let equal (a : t) (b : t) =
    String.(a.name = b.name) &&
    String.Map.equal Bit.Vector.equal a.args b.args

  let to_string ({name;args} : t) : string =
    let open Printf in 
    Map.fold args ~init:"" ~f:(fun ~key ~data acc -> 
      let argstr = sprintf "%s = %s" key (Bit.Vector.to_string data) in 
      if String.length acc = 0 then 
        argstr
      else 
        sprintf "%s, %s" acc argstr
    )
    |> sprintf "%s(%s)" name

  let nullary name = {name; args = String.Map.empty}


  let get_name action = action.name
  let has_name (action : t) name = 
    String.(action.name = name)
  let set_name name action =
    {action with name}

  let has_data (action : t) = Map.mem action.args

  let get_datum (action : t) (name : string) = 
    Map.find action.args name

  let get_data (action : t) = action.args

  let get_datum_exn (action : t) (name : string) =
    get_datum action name
    |> Option.value_exn ~message:(Printf.sprintf "Couldnt find action data param %s" name)

  let get_datum' = Fun.flip get_datum

  let get_datum_exn' = Fun.flip get_datum_exn

  let project_data (params : string list) (action : t) = 
    {action with args =
      Map.filter_keys action.args ~f:String.(List.mem params ~equal)}

  let update_data action b v =
    { action with args = 
      Map.set action.args ~key:b ~data:v
    }

  let pair a1 a2 ~f  =
    let args = Map.merge a1.args a2.args ~f:(fun ~key -> function 
      | `Both (bv1, bv2) when Bit.Vector.equal bv1 bv2 ->  Some bv1
      | `Both (bv1, bv2) -> failwithf "error merging action data---collision on %s (%s <> %s)" (key)  (Bit.Vector.to_string bv1) (Bit.Vector.to_string bv2) ()
      | `Left bv -> Some bv
      | `Right bv -> Some bv
    ) in 
    {name = f (a1.name, a2.name); args}
    

end

module MatchAction = struct 
  type t = {
    matches : Match.t String.Map.t;
    action : Action.t;
  }

  let make matches action = {matches;action}

  let keys_widths row = 
    Map.fold row.matches ~init:[] ~f:(fun ~key ~data kws -> 
      let width = Match.length data in 
      kws @ [key, width]
    )

  let to_string ({matches; action}: t) = 
    Printf.sprintf "\t%s -> %s" 
      (Map.to_alist matches |> List.map ~f:(fun (x,m) -> Printf.sprintf "'%s' ~ %s" x (Match.to_string m)) |> String.concat ~sep:", ")
      (Action.to_string action)

  let equal (ma : t) (ma' : t) =
    String.Map.equal Match.equal ma.matches ma'.matches 
    && Action.equal ma.action ma'.action

  let get_match (ma : t) name = 
    Map.find_exn ma.matches name

  let get_field (ma : t) name =
    match Action.get_datum ma.action name with 
    | None -> get_match ma name
    | Some v -> Match.Exact v

  let does_match keys ({matches;action=_} : t) =
    Map.for_alli matches ~f:(fun ~key:x ~data:mtch -> 
      match Map.find keys x with 
      | None -> false
      | Some value -> 
        Match.matches value mtch
    )

  let runs_action name (ma : t) = Action.has_name ma.action name

  let restrict_keys ma keys = 
    {ma with 
      matches = Map.filter_keys ma.matches ~f:(String.(List.mem keys ~equal))
    }
    
  let get_action (ma : t) : Action.t = ma.action
  let get_matches (ma : t) : Match.t String.Map.t = ma.matches

  let pair (row1 : t) (row2 : t) ~f = 
    let (let+) o f = Option.map o ~f in 
    let (let*) o f = Option.bind o ~f in 
    let match_keys = Map.(
      keys row1.matches @ keys row2.matches 
      |> List.dedup_and_sort ~compare:String.compare)
      (* remove duplicates lets us use 'add' below, triggering exceptions if we've screwed up *)
    in 
    let+ matches = 
      List.fold match_keys ~init:(Some String.Map.empty) ~f:(fun opt_isect key -> 
        let* intersection = opt_isect in 
        match Map.(find row1.matches key, find row2.matches key) with 
        | None, None -> failwith "error: impossible" 
        | Some data, None | None, Some data ->
          Some (Map.add_exn intersection ~key ~data)
        | Some d1, Some d2 -> 
          let+ data = Match.intersect d1 d2 in 
          Map.set intersection ~key ~data
      )
    in
    let action = Action.pair row1.action row2.action ~f in 
    { matches; action }

    let empty_intersection row1 row2 =
      Map.merge row1.matches row2.matches ~f:(fun ~key:_ -> function 
        | `Both (m1, m2) -> Some (m1,m2)
        | _ -> None
      ) |> 
      Map.exists ~f:(fun (m1,m2) -> 
        Match.empty_intersection m1 m2
      )

    let nonempty_intersection row1 row2 = not (empty_intersection row1 row2)

end

module MatchActionTable = struct 
  type t = MatchAction.t list

  let length = List.length

  let of_alist keys = List.map ~f:(fun (data, action) ->
    let matches = 
      List.zip_exn keys data
      |> String.Map.of_alist_exn
    in
    MatchAction.{matches;action})

  let keys (tbl : t) = 
    let sort = List.sort ~compare:(fun (s, _) (s',_) -> String.compare s s') in
    let (==) = List.equal (Tuple2.equal ~eq1:String.equal ~eq2:Int.equal) in 
    List.fold tbl ~init:None ~f:(fun keysopt row -> 
      let keys' = MatchAction.keys_widths row |> sort in 
      match keysopt with 
      | None -> Some keys'
      | Some keys ->
        if keys == keys' then 
          Some keys
        else 
          failwith "Match Action table rows had different key sets"      
    ) |> Option.value_exn ~message:"table was empty, couldn't get keys"

  let actions : t -> Action.t list =
    List.map ~f:(fun (row : MatchAction.t) -> row.action)

  let equal = List.equal MatchAction.equal

  let to_string mas = 
    mas
    |> List.map ~f:(fun row -> MatchAction.to_string row)
    |> String.concat ~sep:"\n"

  let find_match (entries : t) keys = 
    List.find entries ~f:(fun row -> MatchAction.does_match keys row)
    |> Option.value_exn ~message:"Couldnt find any matching rows in table"

  let run (entries : t) keys = 
    let entry = find_match entries keys in 
    entry.action

  let get_matches name entries = 
    List.map entries ~f:(fun row -> MatchAction.get_match row name)

  let get_actions (name: string) entries = 
    List.filter entries ~f:(MatchAction.runs_action name)
    |> List.map ~f:(fun (ma : MatchAction.t) -> ma.action)

  let map ~f : t -> t= 
    List.map ~f

  let bind ~f : t -> t =
    List.bind ~f

  let size (mat : t) =
    List.length mat

  let (<+) tbl new_rules =
    new_rules @ tbl

  end
