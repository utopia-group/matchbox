[@@@warning "-32"]

open Core
open Matchbox
open Alcotest

let f i = BaseLogic.Symbol.make (sprintf "F%d" i) [] 0

let create_basic_type_context () : Type.ctx =
  let open Type in
  Map.of_alist_exn
    (module String)
    [
      ( "F0",
        Table
          {
            keys =
              Map.of_alist_exn
                (module String)
                [
                  ("src_ip", (32, Exact));
                  ("dst_ip", (32, Exact));
                  ("src_port", (16, Exact));
                ];
            actions = ["fwd"; "drop"; "route"];
            data =
              Map.of_alist_exn (module String) [("port", 16); ("next_hop", 32)];
          } );
      ( "F1",
        Table
          {
            keys =
              Map.of_alist_exn
                (module String)
                [("vlan_id", (16, Exact)); ("protocol", (8, Exact))];
            actions = ["allow"; "deny"; "tag_vlan"; "mirror"];
            data =
              Map.of_alist_exn
                (module String)
                [("vlan_tag", 16); ("mirror_port", 16)];
          } );
      ( "F2",
        Table
          {
            keys =
              Map.of_alist_exn
                (module String)
                [("dst_port", (16, Exact)); ("priority", (8, Exact))];
            actions = ["fwd"; "load_balance"; "broadcast"];
            data =
              Map.of_alist_exn (module String) [("action", 32); ("weight", 8)];
          } );
      ( "F3",
        Table
          {
            keys =
              Map.of_alist_exn
                (module String)
                [("src_ip", (32, Exact)); ("dst_ip", (32, Exact))];
            actions = ["encap"; "decap"; "rewrite"];
            data =
              Map.of_alist_exn
                (module String)
                [("tunnel_id", 32); ("new_header", 64)];
          } );
    ]

let create_extended_type_context () : Type.ctx =
  let basic_ctx = create_basic_type_context () in
  let open Type in
  List.fold (List.range 4 32) ~init:basic_ctx ~f:(fun acc i ->
      let name = sprintf "F%d" i in
      let table =
        {
          keys =
            Map.of_alist_exn
              (module String)
              [("src_ip", (32, Exact)); ("dst_ip", (32, Exact))];
          actions = ["fwd"; "drop"];
          data =
            Map.of_alist_exn (module String) [("port", 16); ("next_hop", 32)];
        }
      in
      Map.set acc ~key:name ~data:(Table table))

let create_transformation_context () : Type.ctx =
  let basic_ctx = create_extended_type_context () in
  let open Type in
  List.fold
    [
      ("new_dst", Match (32, Exact));
      ("base_vlan", Match (16, Exact));
      ("target_port", Match (16, Exact));
    ]
    ~init:basic_ctx
    ~f:(fun acc (key, data) -> Map.set acc ~key ~data)

let test_id () =
  let open BaseLogic in
  let type_ctx = create_basic_type_context () in
  let target = f 2 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Id f' -> Symbol.(f' = target) && Symbol.(cand.defined = target)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  check bool "Found at least one Id(F2)" true (not (Set.is_empty progs));
  let identity_prog =
    Set.find_exn progs ~f:(fun p ->
        match p.definition with Clause.Id _ -> true | _ -> false)
  in
  match identity_prog with
  | {defined; definition = Clause.Id f'} ->
    check string "Defined is F2" "F2" defined.name;
    check string "Id is F2" "F2" f'.name
  | _ -> fail "Expected Clause.Id F2"

let test_compose () =
  let open BaseLogic in
  let type_ctx = create_basic_type_context () in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Compose (g, h) -> String.(g.name = "F0" && h.name = "F1")
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  check bool "Found at least one composition" true (not (Set.is_empty progs));
  let compose_prog =
    Set.find_exn progs ~f:(fun p ->
        match p.definition with
        | Clause.Compose (g, h) -> String.(g.name = "F0" && h.name = "F1")
        | _ -> false)
  in
  match compose_prog.definition with
  | Clause.Compose (g, h) ->
    check string "Compose left is F0" "F0" g.name;
    check string "Compose right is F1" "F1" h.name;
    (* Verify that defined symbol is new/different *)
    check bool "Defined symbol is not F0" true
      (not String.(compose_prog.defined.name = "F0"));
    check bool "Defined symbol is not F1" true
      (not String.(compose_prog.defined.name = "F1"))
  | _ -> fail "Expected Clause.Compose(F0,F1)"

let test_invert () =
  let open BaseLogic in
  let type_ctx = create_basic_type_context () in
  let target = f 3 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Invert f' -> Symbol.(f' = target) && Symbol.(cand.defined = target)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  check bool "Found at least one Invert(F3)" true (not (Set.is_empty progs));
  let inv_prog =
    Set.find_exn progs ~f:(fun p ->
        match p.definition with Clause.Invert _ -> true | _ -> false)
  in
  match inv_prog with
  | {defined; definition = Clause.Invert f'} ->
    check string "Defined is F3" "F3" defined.name;
    check string "Invert is F3" "F3" f'.name
  | _ -> fail "Expected Clause.Invert F3"

(* Test that synthesizer can find both Id and Invert for different symbols *)
let test_multiple_clause_kinds () =
  let open BaseLogic in
  let type_ctx = create_basic_type_context () in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Id f' when String.(f'.name = "F0") -> true
    | Clause.Invert f' when String.(f'.name = "F1") -> true
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  let has_id =
    Set.exists progs ~f:(fun p ->
        match p.definition with
        | Clause.Id f' when String.(f'.name = "F0") -> true
        | _ -> false)
  in
  let has_inv =
    Set.exists progs ~f:(fun p ->
        match p.definition with
        | Clause.Invert f' when String.(f'.name = "F1") -> true
        | _ -> false)
  in
  check bool "Has identity clause" true has_id;
  check bool "Has Invert clause" true has_inv;
  check bool "Found both clause types" true (has_id && has_inv)

let test_10_way_compose () =
  let open BaseLogic in
  let composition_patterns : (string * string) list =
    [
      ("F0", "F1");
      ("F2", "F3");
      ("F4", "F5");
      ("F6", "F7");
      ("F8", "F9");
      ("F10", "F11");
      ("F12", "F13");
      ("F14", "F15");
      ("F16", "F17");
      ("F18", "F19");
    ]
  in
  let phi (cand : BaseLogic.t) : bool =
    match cand.definition with
    | Clause.Compose (g, h) ->
      List.exists composition_patterns ~f:(fun (rhs1, rhs2) ->
          String.(g.name = rhs1 && h.name = rhs2))
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  let assignments =
    Set.to_list progs
    |> List.map ~f:(fun (prog : BaseLogic.t) ->
           match prog.definition with
           | Clause.Compose (g, h) ->
             sprintf "%s := Compose(%s,%s)" prog.defined.name g.name h.name
           | _ -> "non-compose")
  in
  let assignment_msg = String.concat ~sep:"; " assignments in
  check string "Concrete LHS assignments verified"
    (String.length assignment_msg > 0 |> string_of_bool)
    "true";
  check int "Found all 10 composition patterns" 10 (Set.length progs);
  List.iter composition_patterns ~f:(fun (rhs1, rhs2) ->
      let found =
        Set.exists progs ~f:(fun (prog : BaseLogic.t) ->
            match prog.definition with
            | Clause.Compose (g, h) -> String.(g.name = rhs1 && h.name = rhs2)
            | _ -> false)
      in
      check bool (sprintf "Contains Fx := Compose(%s,%s)" rhs1 rhs2) true found);
  Set.iter progs ~f:(fun (prog : BaseLogic.t) ->
      match prog.definition with
      | Clause.Compose (g, h) ->
        (* Verify LHS symbol is different from RHS *)
        check bool
          (sprintf "LHS %s is concrete and distinct from RHS %s,%s"
             prog.defined.name g.name h.name)
          true
          (not
             String.(prog.defined.name = g.name || prog.defined.name = h.name))
      | _ -> fail "Expected only Compose clauses")

let test_join () =
  let open BaseLogic in
  let type_ctx = create_basic_type_context () in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Join (f, g, _) -> String.(f.name = "F0" && g.name = "F1")
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  check bool "Found at least one join" true (not (Set.is_empty progs));
  let join_prog =
    Set.find_exn progs ~f:(fun p ->
        match p.definition with Clause.Join _ -> true | _ -> false)
  in
  match join_prog.definition with
  | Clause.Join (f, g, _) ->
    check string "Join left is F0" "F0" f.name;
    check string "Join right is F1" "F1" g.name;
    check bool "Defined symbol is not F0" true
      (not String.(join_prog.defined.name = "F0"));
    check bool "Defined symbol is not F1" true
      (not String.(join_prog.defined.name = "F1"))
  | _ -> fail "Expected Clause.Join(F0,F1,[])"

let test_join_with_alignment () =
  let open BaseLogic in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Join (f, g, alignment) ->
      String.(f.name = "F0" && g.name = "F1")
      && List.exists alignment ~f:(fun ((a1, a2), result) ->
             String.(a1 = "fwd" && a2 = "allow" && result = "fwd_allow"))
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found join with concrete alignment (fwd, allow) -> fwd_allow" true
    (not (Set.is_empty progs));
  let join_prog =
    Set.find_exn progs ~f:(fun p ->
        match p.definition with
        | Clause.Join (_, _, alignment) ->
          List.exists alignment ~f:(fun ((a1, a2), result) ->
              String.(a1 = "fwd" && a2 = "allow" && result = "fwd_allow"))
        | _ -> false)
  in
  match join_prog.definition with
  | Clause.Join (f, g, alignment) ->
    check string "Join left is F0" "F0" f.name;
    check string "Join right is F1" "F1" g.name;
    check bool "Defined symbol is not F0" true
      (not String.(join_prog.defined.name = "F0"));
    check bool "Defined symbol is not F1" true
      (not String.(join_prog.defined.name = "F1"));
    check bool "Alignment contains expected mapping" true
      (List.exists alignment ~f:(fun ((a1, a2), result) ->
           String.(a1 = "fwd" && a2 = "allow" && result = "fwd_allow")))
  | _ -> fail "Expected Clause.Join with non-empty alignment"

let test_join_specific_alignments () =
  let open BaseLogic in
  let test_fwd_drop () =
    let phi (cand : t) =
      match cand.definition with
      | Clause.Join (f, g, alignment) ->
        String.(f.name = "F0" && g.name = "F1")
        && List.exists alignment ~f:(fun ((a1, a2), result) ->
               String.(a1 = "fwd" && a2 = "drop" && result = "fwd_drop"))
      | _ -> false
    in
    let progs = BaseSynthesizer.synth phi in
    check bool "Found join with concrete alignment (fwd, drop) -> fwd_drop" true
      (not (Set.is_empty progs))
  in

  let test_route_mirror () =
    let phi (cand : t) =
      match cand.definition with
      | Clause.Join (f, g, alignment) ->
        String.(f.name = "F0" && g.name = "F1")
        && List.exists alignment ~f:(fun ((a1, a2), result) ->
               String.(a1 = "route" && a2 = "mirror" && result = "route_mirror"))
      | _ -> false
    in
    let progs = BaseSynthesizer.synth phi in
    check bool
      "Found join with concrete alignment (route, mirror) -> route_mirror" true
      (not (Set.is_empty progs))
  in

  let test_multi_mapping_concrete () =
    let phi (cand : t) =
      match cand.definition with
      | Clause.Join (f, g, alignment) ->
        String.(f.name = "F0" && g.name = "F1")
        && List.exists alignment ~f:(fun ((a1, a2), result) ->
               String.(
                 a1 = "fwd" && a2 = "tag_vlan" && result = "fwd_with_vlan"))
        && List.exists alignment ~f:(fun ((a1, a2), result) ->
               String.(a1 = "drop" && a2 = "tag_vlan" && result = "drop_tagged"))
      | _ -> false
    in
    let progs = BaseSynthesizer.synth phi in
    check bool "Found join with concrete multi-mapping alignment" true
      (not (Set.is_empty progs))
  in

  test_fwd_drop ();
  test_route_mirror ();
  test_multi_mapping_concrete ()

let test_join_multi_mapping () =
  let open BaseLogic in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Join (f, g, alignment) ->
      String.(f.name = "F0" && g.name = "F1")
      && List.exists alignment ~f:(fun ((a1, a2), result) ->
             String.(a1 = "fwd" && a2 = "tag_vlan" && result = "fwd_with_vlan"))
      && List.exists alignment ~f:(fun ((a1, a2), result) ->
             String.(a1 = "drop" && a2 = "tag_vlan" && result = "drop_tagged"))
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found concrete multi-mapping join with fwd+tag_vlan pattern" true
    (not (Set.is_empty progs));
  let multi_join_prog =
    Set.find_exn progs ~f:(fun p ->
        match p.definition with
        | Clause.Join (_, _, alignment) ->
          List.exists alignment ~f:(fun ((a1, a2), result) ->
              String.(a1 = "fwd" && a2 = "tag_vlan" && result = "fwd_with_vlan"))
          && List.exists alignment ~f:(fun ((a1, a2), result) ->
                 String.(
                   a1 = "drop" && a2 = "tag_vlan" && result = "drop_tagged"))
        | _ -> false)
  in
  match multi_join_prog.definition with
  | Clause.Join (f, g, alignment) ->
    check bool "Defined symbol is not F0" true
      (not String.(multi_join_prog.defined.name = "F0"));
    check bool "Defined symbol is not F1" true
      (not String.(multi_join_prog.defined.name = "F1"));
    check string "Join left is F0" "F0" f.name;
    check string "Join right is F1" "F1" g.name;
    check bool "Contains fwd+tag_vlan->fwd_with_vlan mapping" true
      (List.exists alignment ~f:(fun ((a1, a2), result) ->
           String.(a1 = "fwd" && a2 = "tag_vlan" && result = "fwd_with_vlan")));
    check bool "Contains drop+tag_vlan->drop_tagged mapping" true
      (List.exists alignment ~f:(fun ((a1, a2), result) ->
           String.(a1 = "drop" && a2 = "tag_vlan" && result = "drop_tagged")))
  | _ -> fail "Expected Clause.Join with concrete multi-mapping alignment"

(* Test that synthesizer can find various kinds of clauses for the same target *)
let test_synthesis_variety () =
  let open BaseLogic in
  let target = f 0 in
  let phi (cand : t) =
    Symbol.(cand.defined = target)
    &&
    match cand.definition with
    | Clause.Id f' -> Symbol.(f' = target)
    | Clause.Invert f' -> Symbol.(f' = target)
    | Clause.MapOut (f', _) -> Symbol.(f' = target)
    | Clause.MapIn (f', _) -> Symbol.(f' = target)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found multiple synthesis options" true (Set.length progs >= 2);
  check bool "Has identity" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with Clause.Id _ -> true | _ -> false));
  check bool "Has Invert" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with Clause.Invert _ -> true | _ -> false))

(* Test synthesis of various ActionTfx transformations *)
let test_mapout_action_transformations () =
  let open BaseLogic in
  let type_ctx = create_transformation_context () in
  let target = f 0 in
  let sample_data = Bit.Vector.of_int ~width:32 42 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.MapOut (f', tfx) when Symbol.(f' = target) -> (
      match tfx with
      | ActionTfx.Project [] -> true
      | ActionTfx.Project
          ["src_ip"; "dst_ip"; "src_port"; "dst_port"; "vlan_id"; "protocol"] ->
        true
      | ActionTfx.Project ["src_ip"; "dst_ip"] -> true
      | ActionTfx.SetTo ("action", ActionTfx.Data data)
        when Bit.Vector.compare data sample_data = 0 ->
        true
      | ActionTfx.SetTo ("dst_ip", ActionTfx.Var "new_dst") -> true
      | ActionTfx.SetTo
          ("vlan_id", ActionTfx.AddK (ActionTfx.Var "base_vlan", _)) ->
        true
      | ActionTfx.Filter _ -> true
      | _ -> false)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  check bool "Found MapOut with various transformations" true
    (Set.length progs >= 4);
  check bool "Has Project transformation" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with
         | Clause.MapOut (_, ActionTfx.Project _) -> true
         | _ -> false));
  check bool "Has SetTo transformation" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with
         | Clause.MapOut (_, ActionTfx.SetTo (_, _)) -> true
         | _ -> false));
  check bool "Has Filter transformation" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with
         | Clause.MapOut (_, ActionTfx.Filter _) -> true
         | _ -> false))

(* Test synthesis of various MatchTfx transformations *)
let test_mapin_match_transformations () =
  let open BaseLogic in
  let type_ctx = create_transformation_context () in
  let target = f 0 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.MapIn (f', tfx) when Symbol.(f' = target) -> (
      match tfx with
      | MatchTfx.Project [] -> true
      | MatchTfx.Project fields when List.length fields > 0 -> true
      | MatchTfx.SetTo (_, MatchTfx.Match _) -> true
      | MatchTfx.SetTo (_, MatchTfx.Var _) -> true
      | MatchTfx.SetTo (_, MatchTfx.AddK (_, _)) -> true
      | MatchTfx.Filter _ -> true
      | _ -> false)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  check bool "Found MapIn with various transformations" true
    (Set.length progs >= 4);
  check bool "Has Project transformation" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with
         | Clause.MapIn (_, MatchTfx.Project _) -> true
         | _ -> false));
  check bool "Has SetTo transformation" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with
         | Clause.MapIn (_, MatchTfx.SetTo (_, _)) -> true
         | _ -> false));
  check bool "Has Filter transformation" true
    (Set.exists progs ~f:(fun p ->
         match p.definition with
         | Clause.MapIn (_, MatchTfx.Filter _) -> true
         | _ -> false))

(* Test specific ActionTfx transformation types *)
let test_specific_action_transformations () =
  let open BaseLogic in
  let type_ctx = create_transformation_context () in
  let target = f 0 in
  let sample_data = Bit.Vector.of_int ~width:32 42 in
  let phi_setto_data (cand : t) =
    match cand.definition with
    | Clause.MapOut (f', ActionTfx.SetTo ("action", ActionTfx.Data data))
      when Symbol.(f' = target) && Bit.Vector.compare data sample_data = 0 ->
      true
    | _ -> false
  in
  let progs_data =
    BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi_setto_data
  in
  check bool "Found SetTo with Data" true (not (Set.is_empty progs_data));
  let phi_setto_addk (cand : t) =
    match cand.definition with
    | Clause.MapOut
        ( f',
          ActionTfx.SetTo
            ("vlan_id", ActionTfx.AddK (ActionTfx.Var "base_vlan", _)) )
      when Symbol.(f' = target) ->
      true
    | _ -> false
  in
  let progs_addk =
    BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi_setto_addk
  in
  check bool "Found SetTo with AddK" true (not (Set.is_empty progs_addk));
  let phi_project_fields (cand : t) =
    match cand.definition with
    | Clause.MapOut (f', ActionTfx.Project ["src_ip"; "dst_ip"])
      when Symbol.(f' = target) ->
      true
    | _ -> false
  in
  let progs_project =
    BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi_project_fields
  in
  check bool "Found Project with specific fields" true
    (not (Set.is_empty progs_project))

(* Test specific MatchTfx transformation types *)
let test_specific_match_transformations () =
  let open BaseLogic in
  let type_ctx = create_transformation_context () in
  let target = f 0 in
  let sample_match_data = Bit.Vector.of_int ~width:32 192 in
  let phi_setto_match (cand : t) =
    match cand.definition with
    | Clause.MapIn
        ( f',
          MatchTfx.SetTo ("src_ip", MatchTfx.Match (Semantics.Match.Exact data))
        )
      when Symbol.(f' = target) && Bit.Vector.compare data sample_match_data = 0
      ->
      true
    | _ -> false
  in
  let progs_match =
    BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi_setto_match
  in
  check bool "Found SetTo with Match" true (not (Set.is_empty progs_match));
  let phi_setto_addk (cand : t) =
    match cand.definition with
    | Clause.MapIn
        ( f',
          MatchTfx.SetTo ("vlan_id", MatchTfx.AddK (MatchTfx.Var "base_vlan", _))
        )
      when Symbol.(f' = target) ->
      true
    | _ -> false
  in
  let progs_addk =
    BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi_setto_addk
  in
  check bool "Found SetTo with AddK" true (not (Set.is_empty progs_addk));
  let phi_filter (cand : t) =
    match cand.definition with
    | Clause.MapIn (f', MatchTfx.Filter filter_map)
      when Symbol.(f' = target) && Map.mem filter_map "protocol" ->
      true
    | _ -> false
  in
  let progs_filter =
    BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi_filter
  in
  check bool "Found Filter with specific field" true
    (not (Set.is_empty progs_filter))

(* Test that synthesis still works for combined transformation types *)
let test_mixed_transformation_synthesis () =
  let open BaseLogic in
  let type_ctx = create_transformation_context () in
  let target = f 0 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.MapOut (f', tfx) when Symbol.(f' = target) -> (
      match tfx with
      | ActionTfx.Project [] -> true
      | ActionTfx.Project fields when List.length fields > 0 -> true
      | ActionTfx.SetTo (_, _) -> true
      | ActionTfx.Filter _ -> true
      | _ -> false)
    | Clause.MapIn (f', tfx) when Symbol.(f' = target) -> (
      match tfx with
      | MatchTfx.Project [] -> true
      | MatchTfx.Project fields when List.length fields > 0 -> true
      | MatchTfx.SetTo (_, _) -> true
      | MatchTfx.Filter _ -> true
      | _ -> false)
    (* Remove Id and Invert to force exploration of MapOut/MapIn *)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth ~type_ctx:(Some type_ctx) phi in
  let mapout_count =
    Set.count progs ~f:(fun p ->
        match p.definition with Clause.MapOut _ -> true | _ -> false)
  in
  let mapin_count =
    Set.count progs ~f:(fun p ->
        match p.definition with Clause.MapIn _ -> true | _ -> false)
  in
  check bool "Has MapOut transformations" true (mapout_count > 0);
  check bool "Has MapIn transformations" true (mapin_count > 0);
  check bool "Has sufficient transformation variety" true
    (mapout_count >= 2 && mapin_count >= 2)
