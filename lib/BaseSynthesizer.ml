open Core
open BaseLogic

let depth = ref (-1)

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

let synth ?(max_depth = 4) (phi : t -> bool) : Set.M(Key).t =
  (* Symbol universe *)
  let symbols : Symbol.t list =
    List.init 32 ~f:(fun i -> Symbol.make (sprintf "F%d" i) [] 0)
  in

  let mk f def : t = {defined = f; definition = def} in

  let seeds : Set.M(Key).t =
    let ids = List.map symbols ~f:(fun f -> mk f (Clause.Id f)) in
    let invs = List.map symbols ~f:(fun f -> mk f (Clause.Invert f)) in
    Set.of_list (module Key) (ids @ invs)
  in

  let _dedup_by_key (xs : t list) : t list =
    fst
      (List.fold_right xs
         ~init:([], Set.empty (module Key))
         ~f:(fun p (acc, ps) ->
           if Set.mem ps p then (acc, ps) else (p :: acc, Set.add ps p)))
  in

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
  in

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
  in

  let expand (p : t) : Set.M(Key).t =
    let f = p.defined in
    let fresh_symbols =
      List.filter symbols ~f:(fun s -> Symbol.compare s f <> 0)
    in
    let base =
      List.take fresh_symbols 4
      |> List.mapi ~f:(fun i new_symbol ->
             match i with
             | 0 -> mk new_symbol (Clause.MapOut (f, ActionTfx.Project []))
             | 1 -> mk new_symbol (Clause.MapIn (f, MatchTfx.Project []))
             | 2 -> mk new_symbol (Clause.Id f)
             | 3 -> mk new_symbol (Clause.Invert f)
             | _ -> failwith "Unexpected index")
    in
    let comps_rebound =
      let all_g_symbols = symbols in
      List.mapi all_g_symbols ~f:(fun i g ->
          let new_defined =
            List.nth_exn fresh_symbols
              (4 + (i % (List.length fresh_symbols - 4)))
          in
          mk new_defined (Clause.Compose (f, g)))
    in
    let joins =
      let alignments = gen_join_alignments () in
      (* Generate joins with multiple g symbols for each alignment *)
      List.concat_mapi alignments ~f:(fun alignment_idx alignment ->
          let g_candidates = List.take symbols 10 in
          (* Try more g symbols *)
          List.mapi g_candidates ~f:(fun g_idx g ->
              (* Ensure we always use a fresh symbol that's not f and not g *)
              let available_symbols =
                List.filter fresh_symbols ~f:(fun s -> Symbol.compare s g <> 0)
              in
              let symbol_idx =
                ((alignment_idx * 10) + g_idx) % List.length available_symbols
              in
              let new_defined = List.nth_exn available_symbols symbol_idx in
              mk new_defined (Clause.Join (f, g, alignment))))
    in
    Set.of_list (module Key) (base @ comps_rebound @ joins)
  in

  depth := 0;

  let scan_layer (layer : Set.M(Key).t) : Set.M(Key).t =
    Set.filter layer ~f:phi
  in

  let rec grow (current_layer : Set.M(Key).t) (seen : Set.M(Key).t) :
      Set.M(Key).t =
    if !depth > max_depth then failwith "Depth limit reached";

    let sols = scan_layer current_layer in
    if not (Set.is_empty sols) then (
      printf "Depth reached: %d\n%!" !depth;
      sols)
    else (
      depth := !depth + 1;

      let grown =
        current_layer
        |> Set.fold
             ~init:(Set.empty (module Key))
             ~f:(fun acc entry -> Set.union acc (expand entry))
        |> Set.filter ~f:(fun p -> not (Set.mem seen p))
      in

      if Set.is_empty grown then failwith "Search space exhausted";

      let seen' = Set.union seen grown in
      grow grown seen')
  in
  grow seeds seeds
