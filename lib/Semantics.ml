open Gpl
open Core
let (let+) r f = Result.map r ~f

module Hardware = struct 
  type t = TCAM | CAM | LPM [@@deriving sexp, compare]
  let to_string = function 
  | TCAM -> "TCAM"
  | CAM -> "CAM"
  | LPM -> "LPM"

  let join h1 h2 = 
    match h1, h2 with 
    | _, TCAM | TCAM,_ -> TCAM
    | CAM, h | h, CAM -> h
    | LPM, LPM -> LPM
end


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

  let of_string str = 
    if String.contains str '*' then 
      Ternary (Trit.Vector.of_string str)
    else match String.lsplit2 str ~on:'/' with 
    | None ->  Exact (Bit.Vector.of_string str)
    | Some (pref, length) -> 
      let n = Int.of_string length in 
      let v = Bit.Vector.of_string pref in 
      Lpm (v,n)


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
    | Lpm (v, _) ->
      (* failwith "TODO: LPM -> TV" *)
      (* TODO: fully implement *)
      Trit.Vector.of_bv v
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

  let ensure_hw_compat m hw =
    let open Hardware in
    match m, hw with
    | Exact _, _ -> true
    | Lpm _, LPM | Lpm _, TCAM -> true
    | Ternary _, TCAM -> true
    | _,_ -> false


  let (||) m1 m2 = 
    match m1, m2 with 
    | Exact bv1, Exact bv2 -> 
      Exact (Bit.Vector.(bv1 || bv2))
    | Ternary tv1, Ternary tv2 ->
      Ternary (Trit.Vector.(tv1 || tv2))
    | Lpm (v1, w1), Lpm (v2,w2) ->
      failwithf "(||) lpm is so hard %s/%d %s/%d" (Bit.Vector.to_string v1) w1 (Bit.Vector.to_string v2) w2 ()
    | _, _ -> 
      failwith "matchkind mismatch"
  
  let (&&) m1 m2 =
    match m1, m2 with 
    | Exact bv1, Exact bv2 -> 
      Exact (Bit.Vector.(bv1 && bv2))
    | Ternary tv1, Ternary tv2 ->
      Ternary (Trit.Vector.(tv1 && tv2))
    | Lpm (v1, w1), Lpm (v2,w2) ->
      failwithf "(&&) lpm is so hard %s/%d %s/%d" (Bit.Vector.to_string v1) w1 (Bit.Vector.to_string v2) w2 ()
    | _, _ -> 
      failwith "matchkind mismatch"

  let (not) = function
    | Exact bv -> Exact (Bit.Vector.not bv)
    | Ternary tv -> Ternary (Trit.Vector.not tv)
    | Lpm (bv, w) -> 
      failwithf "lpm negation! %s %d" (Bit.Vector.to_string bv) w ()

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
    match m1, m2 with
    | Exact v1, Exact v2 -> (
      let tv1 = Trit.Vector.of_bv v1 in
      let tv2 = Trit.Vector.of_bv v2 in
      match Trit.Vector.intersect tv1 tv2 with 
      | None -> None
      | Some tv -> Some (Exact (Trit.Vector.to_bv_exn tv)))
    | Lpm (v1, plen1), Lpm (v2, plen2) when plen1 = plen2 -> (
      let tv1 = Trit.Vector.of_bv v1 in
      let tv2 = Trit.Vector.of_bv v2 in
      match Trit.Vector.intersect tv1 tv2 with 
      | None -> None
      | Some tv -> Some (Lpm (Trit.Vector.to_bv_exn tv, plen1)))
    | Ternary tv1, Ternary tv2 -> (
      match Trit.Vector.intersect tv1 tv2 with 
      | None -> None
      | Some tv -> Some (Ternary tv))
    | Ternary tv, Exact v | Exact v, Ternary tv -> 
      Option.map
        (Trit.Vector.intersect tv (Trit.Vector.of_bv v))
        ~f:(fun tv -> (Exact (Trit.Vector.to_bv_exn tv)))
    | Ternary tv, Lpm (v, _) | Lpm (v, _), Ternary tv ->
      Option.map
        (Trit.Vector.intersect tv (Trit.Vector.of_bv v))
        ~f:(fun tv -> (Lpm (Trit.Vector.to_bv_exn tv, Bit.Vector.length v)))
    | _ -> failwith "TODO"

  let empty_intersection m1 m2 = intersect m1 m2 |> Option.is_none

  let map_to_bexpr (matches : t String.Map.t) : Gpl.BExpr.t = 
    let open Gpl in 
    let open Gpl.BExpr in
    Map.fold matches ~init:true_ ~f:(fun ~key ~data phi -> and_ phi(
        let size = length data in
        let x = Expr.var (Var.make key size) in 
        let v,m = to_mask_pair data in 
        let valu = Expr.bvi (Bit.Vector.to_int v) size in
        let mask = Expr.bvi (Bit.Vector.to_int m) size in 
        TComp(Eq, BinOp(BAnd, x, mask),
                  BinOp(BAnd, valu, mask))))

  let vmap_to_bexpr (vmatches : t Gpl.Var.Map.t) : Gpl.BExpr.t = 
    let matches = Map.fold vmatches ~init:String.Map.empty ~f:(fun ~key ~data -> 
      Map.set ~key:(Gpl.Var.str key) ~data
    ) in
    map_to_bexpr matches

end


module DependentAction = struct
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

module MatchExpression = struct
  type t = Match.t String.Map.t

  let empty = String.Map.empty

  let find : t -> string -> Match.t option = Map.find

  let findv m x = find m (Var.str x)

  let find_exn : t -> string -> Match.t =  Map.find_exn
  
  let findv_exn (matches : t) x = find_exn matches (Var.str x)

  let keys_widths matches = 
    Map.fold matches ~init:[] ~f:(fun ~key ~data kws -> 
        let width = Match.length data in 
        kws @ [key, (width)])

  let keysv matches =
    keys_widths matches
    |> List.map ~f:(fun (name, width) -> 
      Var.make name width
    )

  let does_match pkt (matches : t) =  
    Map.for_alli matches ~f:(fun ~key:x ~data:mtch -> 
      match Map.find pkt x with 
      | None -> false 
      | Some value -> 
        Match.matches value mtch
    )

  let remove (matches : t) s :t = 
    Map.remove matches s

  let removev matches x = remove matches (Var.str x)

  let set (matches : t) s me : t = 
    Map.set matches ~key:s ~data:me

  let setv matches x me : t =
    Map.set matches ~key:(Var.str x) ~data:me

  let project matches names : t = 
    Map.filter_keys matches ~f:String.(List.mem names ~equal)

  let projectv matches xs : t =
    List.map xs ~f:Var.str
    |> project matches

  let intersect m1 m2 = 
    try
      Some (Map.merge m1 m2 ~f:(fun ~key:_ -> function
        | `Left m | `Right m -> Some m
        | `Both (m1,m2) -> 
          match Match.intersect m1 m2 with 
          | Some m -> Some m 
          | _ -> failwith "intersect failed"
      ))
    with
    | _ -> None

end

module Data = struct 
  type t = Bit.Vector.t String.Map.t

  let empty : t = String.Map.empty

  let to_string data = 
    Map.fold data ~init:[] ~f:(fun ~key ~data -> 
      Printf.sprintf "%s=%s" key (Bit.Vector.to_string data)
      |> List.cons 
    )
    |> String.concat ~sep:","

  let equal data1 data2 = 
    Map.equal Bit.Vector.equal data1 data2

  let find : t -> string -> Bit.Vector.t option = Map.find
  let findv data x = find data (Var.str x)
  let find_exn (data : t) s = Map.find_exn data s
  let findv_exn data x = find_exn data (Var.str x)

  let varize data = 
    Map.fold data ~init:Var.Map.empty ~f:(fun ~key ~data ->
      let width = Bit.Vector.length data in 
      let key = Var.make key width in
      Map.set ~key ~data
    )
  let to_gpl_model data = 
    varize data |> 
    Var.Map.map ~f:(fun bv -> 
      let v = Bit.Vector.to_int bv in 
      let bigv = Bigint.of_int v in
      let w = Bit.Vector.length bv in
      (bigv, w)
    )

  let disjoint_union data1 data2 = 
    Map.merge data1 data2 ~f:(fun ~key -> function 
      | `Left bv | `Right bv -> Some bv
      | `Both (bv1, bv2) -> 
        if Bit.Vector.equal bv1 bv2 then 
          Some bv1
        else
          failwithf "Could not disjoint union data %s had different values %s <> %s" key 
            (Bit.Vector.to_string bv1) 
            (Bit.Vector.to_string bv2) ()
    )

  let project data names = Map.filter_keys data ~f:String.(List.mem names ~equal)
  let projectv data xs = List.map xs ~f:Var.str |> project data

  let update (data : t) name value = 
    Map.set data ~key:name ~data:value

  let updatev data x value = 
    update data (Var.str x) value

  let remove (data : t) name =
    Map.remove data name

  let removev data x = remove data (Var.str x)

end

module MagmaAction = struct 
  type t = 
    | Name of string
    | Pair of t * t
    [@@deriving compare, equal, sexp]

  let rec to_string = function 
  | Name s -> s
  | Pair (a1, a2) -> Printf.sprintf "(%s,%s)" (to_string a1) (to_string a2)

  let make s = Name s

  let rec to_list = function 
  | Name s -> [s]
  | Pair (a1, a2) -> to_list a1 @ to_list a2

  let (@) a1 a2 = Pair (a1,a2) 

  let (<@) a s = Pair (a, Name s)

  let (@>) s a = Pair (Name s, a)

end

module MatchAction = struct 
  type t = {
    hw : Hardware.t;
    matches : MatchExpression.t;
    action : MagmaAction.t;
    data : Data.t;
  }

  let make hw matches action data = {hw; matches;action; data}

  let keys_widths row = 
    MatchExpression.keys_widths row.matches

  let to_string ({hw; matches; action; data}: t) = 
    Printf.sprintf "%s<(%s); (%s); (%s)>"
      (Hardware.to_string hw) 
      (Map.to_alist matches |> List.map ~f:(fun (x,m) -> Printf.sprintf "'%s' ~ %s" x (Match.to_string m)) |> String.concat ~sep:", ")
      (MagmaAction.to_string action)
      (Data.to_string data)

  let equal (row : t) (row' : t) =
    String.Map.equal Match.equal row.matches row'.matches 
    && MagmaAction.equal row.action row'.action
    && Data.equal row.data row'.data

  let get_match (row : t) name = 
    Map.find_exn row.matches name

  let get_field (row : t) name =
    match Data.find row.data name with 
    | None -> MatchExpression.find_exn row.matches name
    | Some v -> Match.Exact v

  let exfil_hardware (row : t) =
    match row.hw with 
    | TCAM -> `TCAM
    | CAM -> `CAM
    | LPM -> `LPM

  let does_match pkt (row : t) =
    MatchExpression.does_match pkt row.matches

  let runs_action (a : MagmaAction.t) (row : t) =
    MagmaAction.equal a row.action

  let get_action (ma : t) : MagmaAction.t = ma.action
  let get_matches (ma : t) : MatchExpression.t = ma.matches
  let get_data (ma : t) : Data.t = ma.data

  let pair (row1 : t) (row2 : t) = 
    let (let+) o f = Option.map o ~f in 
    let (let*) o f = Option.bind o ~f in
    let hw = Hardware.join row1.hw row2.hw in
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
    let data = Data.disjoint_union row1.data row2.data in 
    let action = MagmaAction.(row1.action @ row2.action) in 
    { hw; matches; action; data }

  let empty_intersection row1 row2 =
    Map.merge row1.matches row2.matches ~f:(fun ~key:_ -> function 
      | `Both (m1, m2) -> Some (m1,m2)
      | _ -> None
    ) |> 
    Map.exists ~f:(fun (m1,m2) -> 
      Match.empty_intersection m1 m2
    )

  let nonempty_intersection row1 row2 = not (empty_intersection row1 row2)

  let remove_key row name = 
    {row with matches = MatchExpression.remove row.matches name}

  let remove_keyv row x = remove_key row (Var.str x)

  let set_match row name me = 
    {row with matches = MatchExpression.set row.matches name me}

  let set_matchv row x = set_match row (Var.str x)

  let match_projectv row xs = 
    {row with matches = MatchExpression.projectv row.matches xs}

  let match_project row names = 
    {row with matches = MatchExpression.project row.matches names}

  let refine row matches = 
    MatchExpression.intersect row.matches matches
    |> Option.map ~f:(fun matches ->
      {row with matches}
    )

  let update_with_matches_list (row : t) (matches_list : MatchExpression.t list) : t list = 
    List.map matches_list ~f:(fun matches -> {row with matches})
  

end

module MatchActionTable = struct 
  type t = MatchAction.t list

  let length = List.length

  let of_alist hw keys = List.map ~f:(fun (match_list, action, data) ->
    let matches = 
      List.zip_exn keys match_list
      |> String.Map.of_alist_exn
    in
    MatchAction.{hw; matches; action; data})

  let of_domain ~hw ~matches ~action ~data =
    List.map ~f:(fun value ->
      MatchAction.make
        hw
        (Map.of_alist_exn (module String) (matches value))
        (MagmaAction.make (action value))
        (Map.of_alist_exn (module String) (data value))
    )

  let keys (tbl : t) = 
    let sort = List.sort ~compare:(fun (s, _) (s',_) -> String.compare s s') in
    let (==) = List.equal (fun (s1, w1) (s2, w2) -> 
      String.(s1 = s2) && Int.(w1 = w2)) 
    in 
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

  let actions : t -> MagmaAction.t list =
    List.map ~f:(fun (row : MatchAction.t) -> row.action)

  let action_names mat = actions mat

  let data mat = 
    let union = Map.merge ~f:(fun ~key -> function 
      | `Left w -> Some w
      | `Right bv -> Some (Bit.Vector.length bv)
      | `Both (w, bv) -> 
        if Bit.Vector.length bv = w then 
          Some w
        else 
          failwithf "Ill-typed table with different sized data args: %s has length %d but value %s" key w (Bit.Vector.to_string bv) ()
    )
    in
    mat 
    |> List.map ~f:(fun (row : MatchAction.t) -> row.data)
    |> List.fold ~init:String.Map.empty ~f:(fun acc data ->
      union acc data
    )
  
    let hw (rows : t) = 
      List.fold rows ~init:Hardware.CAM ~f:(fun hw row -> 
        Hardware.join hw row.hw  
      )

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
    (entry.action, entry.data)

  let get_matches name entries = 
    List.map entries ~f:(fun row -> MatchAction.get_match row name)

  let map ~f : t -> t = 
    List.map ~f

  let bind ~f : t -> t =
    List.bind ~f

  let agg_bind ~f : t -> t =
    List.fold ~init:[] ~f:(fun above row -> 
      above @ f above row
    )

  let fold ~init ~f : t -> t = List.fold ~init ~f

  let size (mat : t) =
    List.length mat

  let postcons (mat : t) row = mat @ [row]

  let (<+) = postcons

  let (<*) : t -> t -> t = List.append

  module MonadicSyntax = struct
    let (let*) m f : t = bind m ~f
    let (let+) m f : t = map m ~f
    let return row : t = [row]
    let empty = []
  end
end
