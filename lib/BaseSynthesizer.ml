open Core
open BaseLogic

let depth = ref (-1)
let typecheck_pruned = ref 0
let total_cands = ref 0
let get_typecheck_stats () : int * int = (!typecheck_pruned, !total_cands)

let typecheck_cand (ctx : Type.ctx option) (cand : t) : bool =
  incr total_cands;
  match ctx with
  | None -> true
  | Some type_ctx -> (
    try
      match Map.find type_ctx cand.defined.name with
      | None ->
        (* TODO: for now assume unknown symbols are valid *)
        true
      | Some _ ->
        let _ = BaseChecker.clause_type type_ctx cand.definition in
        true
    with _ ->
      incr typecheck_pruned;
      false)

module Key = struct
  module T = struct
    type t = BaseLogic.t

    let sexp_of_t = BaseLogic.sexp_of_t
    let t_of_sexp = BaseLogic.t_of_sexp
    let compare = BaseLogic.compare
  end

  include T
  include Comparable.Make (T)
end

(* Symbol universe *)
let symbols : Symbol.t list =
  List.init 32 ~f:(fun i -> Symbol.make (sprintf "F%d" i) [] 0)

let mk f def : t = {defined = f; definition = def}

let seeds : Set.M(Key).t =
  let ids = List.map symbols ~f:(fun f -> mk f (Clause.Id f)) in
  Set.of_list (module Key) ids

let action_pool =
  [
    "fwd";
    "drop";
    "route";
    "tag_vlan";
    "load_balance";
    "mirror";
    "allow";
    "deny";
    "broadcast";
    "flood";
    "setgroup_eth";
    "setgroup_ipv4";
    "setgroup_tcp";
    "default";
    "encap";
    "decap";
    "rewrite";
    "redirect";
    "punt";
    "trap";
  ]

let gen_join_alignments () : ((string * string) * string) list list =
  let pairs = List.cartesian_product action_pool action_pool in

  let single_mappings =
    List.take pairs 25
    |> List.map ~f:(fun (a1, a2) -> [((a1, a2), sprintf "%s_%s" a1 a2)])
  in
  let multi_mappings =
    [
      [
        (("fwd", "tag_vlan"), "fwd_with_vlan");
        (("drop", "tag_vlan"), "drop_tagged");
      ];
      [
        (("route", "mirror"), "route_mirror");
        (("fwd", "drop"), "conditional_fwd");
      ];
      [
        (("allow", "setgroup_eth"), "allow_with_group");
        (("deny", "setgroup_ipv4"), "deny_with_group");
      ];
    ]
  in
  [[]] @ single_mappings @ multi_mappings

let gen_action_tfxs () : ActionTfx.t list =
  let field_names =
    ["src_ip"; "dst_ip"; "src_port"; "dst_port"; "vlan_id"; "protocol"]
  in
  let sample_data = Bit.Vector.of_int ~width:32 42 in
  [
    ActionTfx.Project [];
    ActionTfx.Project field_names;
    ActionTfx.Project ["src_ip"; "dst_ip"];
    ActionTfx.SetTo ("action", ActionTfx.Data sample_data);
    ActionTfx.SetTo ("dst_ip", ActionTfx.Var "new_dst");
    ActionTfx.SetTo
      ( "vlan_id",
        ActionTfx.AddK
          (ActionTfx.Var "base_vlan", Bit.Vector.of_int ~width:16 100) );
    ActionTfx.Filter
      (Map.singleton
         (module String)
         "priority"
         (Semantics.Match.Exact (Bit.Vector.of_int ~width:8 5)));
  ]

let gen_match_tfxs () : MatchTfx.t list =
  let field_names =
    ["src_ip"; "dst_ip"; "src_port"; "dst_port"; "vlan_id"; "protocol"]
  in
  let sample_match = Semantics.Match.Exact (Bit.Vector.of_int ~width:32 192) in
  [
    MatchTfx.Project [];
    MatchTfx.Project field_names;
    MatchTfx.Project ["src_ip"; "dst_ip"];
    MatchTfx.SetTo ("src_ip", MatchTfx.Match sample_match);
    MatchTfx.SetTo ("dst_port", MatchTfx.Var "target_port");
    MatchTfx.SetTo
      ( "vlan_id",
        MatchTfx.AddK (MatchTfx.Var "base_vlan", Bit.Vector.of_int ~width:16 10)
      );
    MatchTfx.Filter (Map.singleton (module String) "protocol" sample_match);
  ]

let expand (p : t) (type_ctx : Type.ctx option) : Set.M(Key).t =
  let f = p.defined in
  let fresh_symbols =
    List.filter symbols ~f:(fun s -> Symbol.compare s f <> 0)
  in
  let base =
    let action_tfxs = gen_action_tfxs () in
    let match_tfxs = gen_match_tfxs () in
    let map_out_count = List.length action_tfxs in
    let map_in_count = List.length match_tfxs in
    let total_count = map_out_count + map_in_count + 2 in
    (* +2 for Id and Invert *)
    List.take fresh_symbols total_count
    |> List.mapi ~f:(fun i new_symbol ->
           if i < map_out_count then
             mk new_symbol (Clause.MapOut (Id f, List.nth_exn action_tfxs i))
           else if i < map_out_count + map_in_count then
             mk new_symbol
               (Clause.MapIn (Id f, List.nth_exn match_tfxs (i - map_out_count)))
           else if i = map_out_count + map_in_count then
             mk new_symbol (Clause.Id f)
           else failwithf "Unexpected index %d" i ())
  in
  let comps_rebound =
    let action_tfxs = gen_action_tfxs () in
    let match_tfxs = gen_match_tfxs () in
    let base_count = List.length action_tfxs + List.length match_tfxs + 2 in
    List.mapi symbols ~f:(fun i g ->
        let new_defined =
          List.nth_exn fresh_symbols
            (base_count + (i % (List.length fresh_symbols - base_count)))
        in
        mk new_defined (Clause.Compose (Id f, Id g)))
  in
  let joins =
    let alignments = gen_join_alignments () in
    List.concat_mapi alignments ~f:(fun alignment_idx alignment ->
        let g_cands = List.take symbols 10 in
        List.mapi g_cands ~f:(fun g_idx g ->
            (* Ensure we always use a fresh symbol that's not f and not g *)
            let available_symbols =
              List.filter fresh_symbols ~f:(fun s -> Symbol.compare s g <> 0)
            in
            let symbol_idx =
              ((alignment_idx * 10) + g_idx) % List.length available_symbols
            in
            let new_defined = List.nth_exn available_symbols symbol_idx in
            mk new_defined (Clause.Join (Id f, Id g, alignment))))
  in
  base @ comps_rebound @ joins
  |> List.filter ~f:(typecheck_cand type_ctx)
  |> Set.of_list (module Key)

let synth ?(max_depth = 4) ?(type_ctx = None) (phi : t -> bool) : Set.M(Key).t =
  depth := 0;
  typecheck_pruned := 0;
  total_cands := 0;
  let rec grow (layer : Set.M(Key).t) (seen : Set.M(Key).t) : Set.M(Key).t =
    if !depth > max_depth then failwith "Depth limit reached";
    let sols =
      Set.filter layer ~f:(fun candidate ->
          typecheck_cand type_ctx candidate && phi candidate)
    in
    if not (Set.is_empty sols) then (
      printf "Depth reached: %d\n%!" !depth;
      (match type_ctx with
      | Some _ ->
        printf "Typechecking stats: %d/%d candidates pruned (%.1f%%)\n%!"
          !typecheck_pruned !total_cands
          (100.0 *. float !typecheck_pruned /. float !total_cands)
      | None -> ());
      sols)
    else (
      depth := !depth + 1;
      let grown =
        layer
        |> Set.fold
             ~init:(Set.empty (module Key))
             ~f:(fun acc entry -> Set.union acc (expand entry type_ctx))
        |> Set.filter ~f:(fun p -> not (Set.mem seen p))
      in
      if Set.is_empty grown then failwith "Search space exhausted";
      let seen' = Set.union seen grown in
      grow grown seen')
  in
  grow seeds seeds
