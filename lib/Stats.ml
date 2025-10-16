type t = {
  name : string;
  typetime : float;
  num_fds : int;
  size_fds : int;
  size : int;
  num_joins : int;
  num_compose : int;
  num_override : int;
  num_filters : int;
  num_tblvars : int;
  num_literals : int;
  num_key_adds : int;
  num_key_dels : int;
  num_data_adds : int;
  num_data_dels : int;
  num_action_renames : int;
  eval_time : float;
  eval_in_size : int;
  eval_out_size : int;
  min_eval_time : float;
  min_eval_size : int;
}[@@deriving yojson]

let empty = 
  {
    name = "";
    typetime = 0.;
    num_fds = 0;
    size_fds = 0;
    size = 0;
    num_joins = 0;
    num_compose = 0;
    num_override = 0;
    num_filters = 0;
    num_tblvars = 0;
    num_literals = 0;
    num_key_adds = 0;
    num_key_dels = 0;
    num_data_adds = 0;
    num_data_dels = 0;
    num_action_renames = 0;
    eval_time = 0.;
    eval_in_size = 0;
    eval_out_size = 0;
    min_eval_time = 0.;
    min_eval_size = 0;
  }

let (+) s1 s2 = 
  { 
    name = String.concat "" [s1.name; s2.name];
    typetime = s1.typetime +. s2.typetime;
    num_fds = s1.num_fds + s2.num_fds;
    size = s1.size + s2.size;
    size_fds = s1.size_fds + s2.size_fds;
    num_joins = s1.num_joins + s2.num_joins;
    num_compose = s1.num_compose + s2.num_compose;
    num_override = s1.num_override + s2.num_override;
    num_filters = s1.num_filters + s2.num_filters;
    num_tblvars = s1.num_tblvars + s2.num_tblvars;
    num_literals = s1.num_literals + s2.num_literals;
    num_key_adds = s1.num_key_adds + s2.num_key_dels;
    num_key_dels = s1.num_key_dels + s2.num_key_dels;
    num_data_adds = s1.num_data_adds + s2.num_data_adds;
    num_data_dels = s1.num_data_dels + s2.num_data_dels;
    num_action_renames = s1.num_action_renames + s2.num_action_renames;
    eval_time = s1.eval_time +. s2.eval_time;
    eval_in_size = s1.eval_in_size + s2.eval_in_size;
    eval_out_size = s1.eval_out_size + s2.eval_out_size;
    min_eval_time = s1.min_eval_time +. s2.min_eval_time;
    min_eval_size = s1.min_eval_size + s2.min_eval_size;
  }

let incr_size s = 
  {s with size = Int.add s.size 1}

let rec analyze (c : BaseLogic.Clause.t) = 
  match c with 
  | Id _ -> 
    {empty with num_tblvars = 1}
    |> incr_size
  | Table _ -> 
    {empty with num_literals = 1}
    |> incr_size
  | Join (c1, c2, _) -> 
    let s = analyze c1 + analyze c2 in 
    {s with num_joins = Int.add s.num_joins 1} 
    |> incr_size
  | Override (c1, c2, _) -> 
    let s = analyze c1 + analyze c2 in 
    {s with num_override = Int.add s.num_override 1} 
    |> incr_size
  | Compose (c1,c2, _) -> 
    let s = analyze c1 + analyze c2 in 
    {s with num_compose = Int.add s.num_compose 1}
    |> incr_size
  | MapOut (c, Del _,_) -> 
    let s = analyze c in
    {s with num_data_dels = Int.add s.num_data_dels 1}
    |> incr_size
  | MapOut (c, SetTo _, _) -> 
    let s = analyze c in 
    {s with num_data_adds = Int.add s.num_data_adds 1}
    |> incr_size
  | MapOut (c, Rename _, _) ->
    let s = analyze c in 
    {s with num_action_renames = Int.add s.num_action_renames 1}
    |> incr_size
  | MapIn (c, Del _, _) -> 
    let s = analyze c in 
    {s with num_key_dels = Int.add s.num_key_dels 1}
    |> incr_size
  | MapIn (c, SetTo _, _) ->
    let s = analyze c in 
    {s with num_key_adds = Int.add s.num_key_adds 1}
    |> incr_size
  | MapIn (c, WildCard _, _) ->
    let s = analyze c in 
    {s with num_key_adds = Int.add s.num_key_adds 1}
    |> incr_size
  | MapIn (c, Filter _, _ ) | MapIn (c, CubeFilter _, _) ->
    let s = analyze c in 
    {s with num_filters = Int.add s.num_filters 1}
  | MapOut (c, Nonce _, _) | MapOut (c, Project _, _) ->
    Printf.eprintf "warning:: not aggregating stats for data map tfx Nonce or Project"; 
    analyze c
    |> incr_size
  | MapIn (c, Project _, _) ->
    Printf.eprintf "warning:: not aggregating stats for key map tfx Project";
    analyze c
    |> incr_size

let print_header () = 
  Printf.printf "name,typetime,num_fds,size_fds,size,num_joins,num_compose,num_override,num_filters,num_tblvars,num_literals,num_key_adds,num_key_dels,num_data_adds,num_data_dels,num_action_renames,eval_time,eval_in_size,eval_out_size,min_eval_size,min_eval_time\n%!"

let println name (stats : t) : unit =
  let stats = {stats with name} in
  Printf.printf "%s,%f,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%f,%d,%d,%d,%f\n%!"
    stats.name
    stats.typetime
    stats.num_fds
    stats.size_fds
    stats.size
    stats.num_joins
    stats.num_compose
    stats.num_override
    stats.num_filters
    stats.num_tblvars
    stats.num_literals
    stats.num_key_adds
    stats.num_key_dels
    stats.num_data_adds
    stats.num_data_dels
    stats.num_action_renames
    stats.eval_time
    stats.eval_in_size
    stats.eval_out_size
    stats.min_eval_size
    stats.min_eval_time
