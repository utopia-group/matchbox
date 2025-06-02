module Queuer = Queue.Make
open Core

let rec sublists xs = 
  match xs with 
  | [] -> [[]]
  | x::xs -> 
    let xs' = sublists xs in 
    let xxs' = List.map xs' ~f:(List.cons x) in
    xs' @ xxs'

let rec bvexp_extend names bvexp =
  let open DSLv2 in 
  match bvexp with
  | BVHole -> 
    Incr BVHole :: 
    Decr BVHole :: 
    List.map names ~f:(fun x -> Var x);
  | Var _ | Lit _ -> []
  | Incr e -> 
    List.map (bvexp_extend names e) ~f:(fun e' -> Incr e')
  | Decr e -> 
    List.map (bvexp_extend names e) ~f:(fun e' -> Decr e')


let rec rexp_extend context = 
  let open DSLv2 in 
  function
  | Id | RenameActionTo _ | DataSlice _ -> []
  | RHole -> 
    let open List in 
    Id ::
    Pipe (RHole, RHole) :: 
    concat [
      Type.get_actions context >>| rename_action_to;
      Type.get_vars context |> sublists >>| data_slice;
      Type.get_vars context >>= (fun name -> 
        [MapKey (name, [], BVHole); MapData (name, [], BVHole)])
    ]
  | MapKey (output, _, b) -> 
    let names = Type.get_vars context in 
    bvexp_extend names b
    |> List.map ~f:(fun b' -> MapKey(output, bvexp_vars b', b'))
  | MapData (output, _, b) -> 
    let names = Type.get_vars context in 
    bvexp_extend names b
    |> List.map ~f:(fun b' -> MapData (output, bvexp_vars b', b'))
  | Pipe (r1, r2) when rexp_hole_free r1 && rexp_hole_free r2 -> []
  | Pipe (r1, r2) when rexp_hole_free r1 -> 
    List.map (rexp_extend context r2) ~f:(fun r2' -> 
      Pipe (r1,r2'))
  | Pipe(r1, r2) when rexp_hole_free r2 -> 
    List.map (rexp_extend context r1) ~f:(fun r1' -> 
      Pipe (r1',r2))
  | Pipe(r1, r2) -> 
    List.bind (rexp_extend context r1) ~f:(fun r1' -> 
      List.map (rexp_extend context r2) ~f:(fun r2' ->
        Pipe(r1', r2')
      )
    )



let extend_callbacks (context : Type.ctx) callbacks = 
  String.Map.fold callbacks ~init:[String.Map.empty] 
    ~f:(fun ~key ~data acc -> 
      List.bind acc ~f:(fun callbacks -> 
        if DSLv2.rexp_hole_free data then 
          [String.Map.set callbacks ~key ~data]
        else 
          List.map (rexp_extend context data) ~f:(fun r -> 
            String.Map.set callbacks ~key ~data:r
          )
      )
    )

let rec extend (context : Type.ctx) exp = 
  let open DSLv2 in 
  match exp with 
  | EHole -> 
    List.concat [
      Type.get_tables context |>
      List.map ~f:(fun tbl -> Table tbl);
      [ Map (EHole, RHole);
        Compose (EHole, EHole);
        Case {table = EHole; callbacks = None}
      ]
    ]
  | Table _ -> []
  | Map (e, r) when exp_hole_free e ->
    List.map (rexp_extend context r) ~f:(fun r' ->  
      Map (e, r')
    )
  | Map (e,r) ->
    extend context e
    |> List.map ~f:(fun e' -> 
      Map (e', r)
    )
  | Compose (e1, e2) -> 
    List.bind (extend context e1) ~f:(fun e1' -> 
      List.map (extend context e2) ~f:(fun e2' -> 
        Compose (e1', e2')
    ))
  | Case {table; callbacks = Some callbacks} when exp_hole_free table ->
    List.map (extend_callbacks context callbacks) ~f:(fun callbacks -> 
      Case {table; callbacks = Some callbacks}
    ) 
  | Case {table; callbacks = None} when exp_hole_free table -> 
    failwith "Need type information to do this sensibly"
  | Case {table; callbacks} -> 
    (* if the table has a hole, callbacks should be a hole *)
    assert (Option.is_none callbacks);
    List.map (extend context table) ~f:(fun table -> 
      Case {table; callbacks = None}
    )


let find_exp names ~f = 
  let open Queuer (struct
    type t = DSLv2.exp
    let prio = DSLv2.exp_size  
  end) in 
  DSLv2.find ~f ~pop ~add_all ~extend:(extend names)