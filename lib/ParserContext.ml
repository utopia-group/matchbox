open Core
open BaseLogic
module T = Type 
module R = ResourceBaseChecker
module F = FDBaseChecker.DepFunDep
module L = BaseLogic

type t = {
    typs : T.ctx;
    rscs : R.ctx;
    gfds : F.itfc_spec;
    assumptions: F.itfc_spec;
    prog : L.t list;
    stats : Stats.t

}
let empty = {
    typs = String.Map.empty;
    rscs = String.Map.empty;
    gfds = String.Map.empty;
    assumptions = String.Map.empty;
    prog = [];
    stats = Stats.empty;
}

let (@) (p1 : t) (p2 : t) : t= 
    { typs = T.(p1.typs @ p2.typs);
        rscs = R.(p1.rscs @ p2.rscs);
        gfds = F.(p1.gfds @ p2.gfds);
        assumptions = F.(p1.assumptions @ p2.assumptions);
        prog = p1.prog @ p2.prog;
        stats = Stats.(p1.stats + p2.stats);
    }

let concat : t list -> t = 
    List.fold ~init:empty ~f:(@)

let add_type (tbl : string) (tau : T.t) (p : t) : t = 
  {p with 
      typs = Map.add_exn p.typs ~key:tbl ~data:tau;
      gfds = Map.add_multi p.gfds ~key:tbl ~data:(F.fd_of_typ tau)
  }

let add_assumption (tbl : string) (fd : F.t) (p : t) : t =
  {p with assumptions = Map.add_multi p.gfds ~key:tbl ~data:fd}

let refine_fds (p : t) : t = 
  let open FDBaseChecker in
  {p with
   gfds = Map.map p.gfds ~f:(fun fds ->
    fds
    |> List.sort ~compare:DepFunDep.compare
    |> List.fold ~init:[] ~f:(fun acc fd ->
      if List.exists acc
        ~f:(fun fd' -> DepFunDep.compare fd fd' >= 0)
      then acc
      else fd :: acc))
  }

let rec complete_clause (clause : Clause.t option) (table : string) (typ : T.t) : Clause.t option =
  Option.map clause ~f:(fun c ->
    match c with
    | Table (_, t, c_typ) ->
      Clause.Table (table,
        List.map t ~f:(fun ma ->
          Semantics.MatchAction.{
            ma with
            hw = typ.hw;
            matches =
            (match
              List.fold2
                (Map.to_alist ma.matches)
                (Map.to_alist typ.keys)
                ~init:(Map.empty (module String))
                (* TODO: typecheck here? *)
                ~f:(fun acc (_, match_) (key, _) -> Map.set acc ~key ~data:match_)
            with
            | Ok matches -> matches
            | Unequal_lengths -> ma.matches);
            data =
            match 
              List.fold2
                (Map.to_alist ma.data)
                (Map.to_alist typ.data)
                ~init:(Map.empty (module String))
                (* TODO: typecheck here? *)
                ~f:(fun acc (_, bv) (key, _) -> Map.set acc ~key ~data:bv)
            with
            | Ok data -> data
            | Unequal_lengths -> ma.data
          }
        ), c_typ)
    | MapIn (c', WildCard x, c_typ) ->
      let w = Map.find_exn typ.keys (Var.str x) in
      let completed_c' = Option.value_exn (complete_clause (Some c') table typ) in
      MapIn (completed_c', WildCard (Var.make (Var.str x) w), c_typ)
    | MapIn (c', tfx, c_typ) -> 
      let completed_c' = Option.value_exn (complete_clause (Some c') table typ) in
      MapIn (completed_c', tfx, c_typ)
    | MapOut (c', tfx, c_typ) -> 
      let completed_c' = Option.value_exn (complete_clause (Some c') table typ) in
      MapOut (completed_c', tfx, c_typ)
    | _ -> c
  )

let create_table rows =
  let open Semantics in
  Clause.table ""
    (List.map rows ~f:(fun (keys, action, data) ->
      MatchAction.make TCAM
        (keys
         |> List.map ~f:(fun bv -> ("", bv |> Trit.Vector.of_string |> Match.Ternary))
         |> Map.of_alist_exn (module String))
        (MagmaAction.make action)
        (data
         |> List.map ~f:(fun bv -> ("", Bit.Vector.of_string bv))
         |> Map.of_alist_exn (module String))
      )
    )

let bulk_create_table decls keys action data =
  let rec make_unique seen data =
    if Set.mem seen (Bit.Vector.to_int data) then
      make_unique seen (Bit.Vector.incr data)
    else
      (data, Set.add seen (Bit.Vector.to_int data))
  in
  let open Semantics in
  let enums, uniques = List.partition_tf decls
    ~f:(function (_, "enumerate", _) -> true
               | (_, "unique", _) -> false
               | _ -> failwith "expected either 'enumerate' or 'unique'")
  in
  enums
  (* Generate all combinations of 'enumerate' fields *)
  |> List.fold ~init:[Map.empty (module String)]
    ~f:(fun acc (x, _, w) ->
      List.map (List.cartesian_product acc (Bit.Vector.enumerate w))
        ~f:(fun (row, a) -> Map.set row ~key:x ~data:a))
  (* Extend each combination with unique values of 'unique' fields *)
  |> List.fold 
    ~init:([], List.fold uniques ~init:(Map.empty (module String))
      ~f:(fun acc (x, _, _) -> Map.set acc ~key:x ~data:(Set.empty (module Int))))
    ~f:(fun (rows, seen) row ->
      let row', seen' =
        List.fold uniques
          ~init:(row, seen)
          ~f:(fun (row, seen) (x, _, w) ->
            let data, seen' = make_unique (Map.find_exn seen x) (Bit.Vector.random w) in
            Map.set row ~key:x ~data, Map.set seen ~key:x ~data:seen')
      in
      row' :: rows, seen')
  |> fst
  (* Make match-action rules *)
  |> List.map ~f:(fun row ->
    MatchAction.make TCAM
      (Map.of_alist_exn
        (module String)
        (List.map keys ~f:(fun k -> k, Match.exact (Map.find_exn row k))))
      (MagmaAction.make action)
      (Map.of_alist_exn
        (module String)
        (List.map data ~f:(fun k -> k, Map.find_exn row k))))
  |> Clause.table ""

let opt_add_def (defined : Symbol.t) (clause : Clause.t option) (p : t) : t =
  match clause with
  | None -> p
  | Some definition -> 
      {p with 
          prog = List.append p.prog [{defined; definition}]
      }

let add_resource_limit table_name limit (p : t) : t= 
  {p with 
    rscs = Map.update p.rscs table_name ~f:(function
      | None -> limit
      | Some other_limit -> Int.min limit other_limit 
    )
  }

let add_gfd table_name gfd (p : t) : t = 
  {p with 
    gfds = Map.update p.gfds table_name ~f:(function
      | None -> [gfd]
      | Some old_gfds -> gfd::old_gfds
    );
    stats = {p.stats with num_fds = p.stats.num_fds + 1;
                          size_fds = p.stats.size_fds + F.size gfd}
  }

let set_typecheck_time t (p : t) : t = 
  {p with
    stats = {p.stats with
      typetime = t
    }
  }

let update_stats clause (p : t) : t =
  match clause with 
  | None -> p
  | Some clause ->
    let stats = Stats.analyze clause in
    {p with 
      stats = Stats.(p.stats + stats) 
    } 


let well_formed ctx (stmt : BaseLogic.t) =
  let annotated = BaseChecker.infer ctx.typs stmt in
  let table_name = Symbol.to_string stmt.defined in 
  let expected_type = Map.find_exn ctx.typs table_name in
  let computed_type = Clause.typeof_exn annotated in
  if not Type.(equal expected_type computed_type) then 
    failwithf "Expected table %s to have type:\n\t%s\nbut it had type:\n\t%s" 
      table_name 
      (Type.to_string expected_type)
      (Type.to_string computed_type) () 
  else
    {defined = stmt.defined; definition = annotated}

let functional ctx ({defined;definition} : BaseLogic.t) = 
  let requirements = Map.find_exn ctx.gfds (Symbol.to_string defined) in
  let had_type_error = ref false in
  List.iter requirements ~f:(fun gfd ->
    let new_spec = F.check ctx.gfds definition gfd in
    let spec = F.remaining_obligations ctx.gfds new_spec in
    Map.iteri spec ~f:(fun ~key ~data ->
      List.iter data ~f:(fun fd ->
        Printf.eprintf "Type Error: %s must satisfy %s\n" key (F.to_string fd);
        had_type_error := true;
      )
    )
  );
  if !had_type_error then failwith "error in the gFD type system";
  {defined;definition}

let appropriately_sized ctx {defined;definition}  = 
  let name = Symbol.to_string defined in 
  match Map.find ctx.rscs name with 
  | None -> {defined;definition}
  | Some maximum ->
    let bound = R.calculate_max_cost ctx.rscs definition in
    if bound > maximum then
      failwithf "table %s supports only %d rules, but its definition could produce %d"
        name maximum bound ()
    else {defined;definition}
      
let typecheck (ctx : t) : t = 
  let c = Clock.start () in
  let prog = 
    List.map ctx.prog ~f:(fun matchstick -> 
      well_formed ctx matchstick
      |> functional {
        ctx with gfds =
        (* Also consider user-provided FD assumptions,
           but not those made on the current table being typechecked *)
        Map.merge ctx.gfds
          (Map.remove ctx.assumptions (Symbol.to_string matchstick.defined))
          ~f:(fun ~key:_ -> function
          | `Left x | `Right x -> Some x
          | `Both (x, y) -> Some (List.append x y)
        )}
      |> appropriately_sized ctx
    )
  in
  let typetime = Clock.stop c in
  {ctx with prog;
            stats = {ctx.stats with typetime}}