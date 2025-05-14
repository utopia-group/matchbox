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
  | Var _ -> []
  | Incr e -> 
    List.map (bvexp_extend names e) ~f:(fun e' -> Incr e')
  | Decr e -> 
    List.map (bvexp_extend names e) ~f:(fun e' -> Decr e')


let rec rexp_extend names = 
  let open DSLv2 in 
  function
  | Id | RenameActionTo _ | DataSlice _ -> []
  | RHole -> 
    let sublists_names = sublists names in
    List.concat [
      [Id; Pipe (RHole, RHole)];
      List.map names ~f:(fun a -> RenameActionTo a);
      List.map sublists_names ~f:(fun ps -> DataSlice ps);
        List.bind names ~f:(fun name -> 
          [
            MapKey (name, [], BVHole);
            MapData (name, [], BVHole);
          ]
        )  
    ]
  | MapKey (output, inputs, b) -> 
    List.map (bvexp_extend names b) ~f:(fun b' -> 
      MapKey(output, inputs, b')
    )
  | MapData (output, _, b) -> 
    List.map (bvexp_extend names b) ~f:(fun b' -> 
      MapData (output, bvexp_vars b', b')
   )
  | Pipe (r1, r2) when rexp_hole_free r1 && rexp_hole_free r2 -> []
  | Pipe (r1, r2) when rexp_hole_free r1 -> 
    List.map (rexp_extend names r2) ~f:(fun r2' -> 
      Pipe (r1,r2'))
  | Pipe(r1, r2) when rexp_hole_free r2 -> 
    List.map (rexp_extend names r1) ~f:(fun r1' -> 
      Pipe (r1',r2))
  | Pipe(r1, r2) -> 
    List.bind (rexp_extend names r1) ~f:(fun r1' -> 
      List.map (rexp_extend names r2) ~f:(fun r2' ->
        Pipe(r1', r2')
      )
    )



let extend_callbacks from callbacks = 
  String.Map.fold callbacks ~init:[String.Map.empty] 
    ~f:(fun ~key ~data acc -> 
      List.bind acc ~f:(fun callbacks -> 
        if DSLv2.rexp_hole_free data then 
          [String.Map.set callbacks ~key ~data]
        else 
          List.map (rexp_extend from data) ~f:(fun r -> 
            String.Map.set callbacks ~key ~data:r
          )
      )
    )

let rec extend names exp = 
  let open DSLv2 in 
  match exp with 
  | EHole -> 
    List.concat [
      List.map names ~f:(fun tbl -> Table tbl);
      [ Map (EHole, RHole);
        Compose (EHole, EHole);
        Case {table = EHole; callbacks = None}
      ]
    ]
  | Table _ -> []
  | Map (e, r) -> 
    List.bind (extend names e) ~f:(fun e' -> 
      if exp_hole_free e' then 
        List.map (rexp_extend names r) ~f:(fun r' -> 
          Map (e', r')
        )
      else
        [e]
    )
  | Compose (e1, e2) -> 
    List.bind (extend names e1) ~f:(fun e1' -> 
      List.map (extend names e2) ~f:(fun e2' -> 
        Compose (e1', e2')
    ))
  | Case {table; callbacks = Some callbacks} when exp_hole_free table ->
    List.map (extend_callbacks names callbacks) ~f:(fun callbacks -> 
      Case {table; callbacks = Some callbacks}
    ) 
  | Case {table; callbacks = None} when exp_hole_free table -> 
    failwith "Need type information to do this sensibly"
  | Case {table; callbacks} -> 
    (* if the table has a hole, callbacks should be a hole *)
    assert (Option.is_none callbacks);
    List.map (extend names table) ~f:(fun table -> 
      Case {table; callbacks = None}
    )


let find_exp names ~f = 
  let open Queuer (struct
    type t = DSLv2.exp
    let prio = DSLv2.exp_size  
  end) in 
  DSLv2.find ~f ~pop ~add_all ~extend:(extend names)