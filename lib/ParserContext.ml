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
    prog : L.t list;
    stats : Stats.t

}
let empty = {
    typs = String.Map.empty;
    rscs = String.Map.empty;
    gfds = String.Map.empty;
    prog = [];
    stats = Stats.empty;
}

let (@) (p1 : t) (p2 : t) : t= 
    { typs = T.(p1.typs @ p2.typs);
        rscs = R.(p1.rscs @ p2.rscs);
        gfds = F.(p1.gfds @ p2.gfds);
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


let well_formed ctx ({defined;definition} : BaseLogic.t) =
  let annotated = BaseChecker.infer ctx.typs definition in
  let table_name = Symbol.to_string defined in 
  let expected_type = Map.find_exn ctx.typs table_name in
  let computed_type = Type.Table (Clause.typeof_exn annotated) in
  if not Type.(equal expected_type computed_type) then 
    failwithf "Expected table %s to have type:\n\t%s\nbut it had type:\n\t%s" 
      table_name 
      (Type.to_string expected_type)
      (Type.to_string computed_type) () 
  else
    {defined; definition = annotated}

let functional ctx ({defined;definition} : BaseLogic.t) = 
  let requirements = Map.find_exn ctx.gfds (Symbol.to_string defined) in
  let had_type_error = ref false in
  List.iter requirements ~f:(fun gfd ->
    let new_spec = F.check ctx.gfds definition gfd in
    let spec = F.remaining_obligations ctx.gfds new_spec in
    Map.iteri spec ~f:(fun ~key ~data ->
      List.iter data ~f:(fun fd ->
        Printf.eprintf "Type Error: %s must satisfy %s" key (F.to_string fd);
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
      |> functional ctx
      |> appropriately_sized ctx
    )
  in
  let typetime = Clock.stop c in
  {ctx with prog;
            stats = {ctx.stats with typetime}}