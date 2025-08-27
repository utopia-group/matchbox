open Core
open Stijl
open Alcotest

let f i = BaseLogic.Symbol.make (sprintf "F%d" i) [] 0

let test_id () =
  let open BaseLogic in
  let target = f 2 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Id f' -> Symbol.(f' = target) && Symbol.(cand.defined = target)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found at least one Id(F2)" true (not (List.is_empty progs));
  let identity_prog =
    List.find_exn progs ~f:(fun p ->
        match p.definition with Clause.Id _ -> true | _ -> false)
  in
  match identity_prog with
  | {defined; definition = Clause.Id f'} ->
    check string "Defined is F2" "F2" defined.name;
    check string "Id is F2" "F2" f'.name
  | _ -> fail "Expected Clause.Id F2"

let test_compose () =
  let open BaseLogic in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Compose (g, h) -> String.(g.name = "F0" && h.name = "F1")
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found at least one composition" true (not (List.is_empty progs));
  let compose_prog =
    List.find_exn progs ~f:(fun p ->
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
  let target = f 3 in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Invert f' -> Symbol.(f' = target) && Symbol.(cand.defined = target)
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found at least one Invert(F3)" true (not (List.is_empty progs));
  let inv_prog =
    List.find_exn progs ~f:(fun p ->
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
  let phi (cand : t) =
    match cand.definition with
    | Clause.Id f' when String.(f'.name = "F0") -> true
    | Clause.Invert f' when String.(f'.name = "F1") -> true
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in

  let has_id =
    List.exists progs ~f:(fun p ->
        match p.definition with
        | Clause.Id f' when String.(f'.name = "F0") -> true
        | _ -> false)
  in
  let has_inv =
    List.exists progs ~f:(fun p ->
        match p.definition with
        | Clause.Invert f' when String.(f'.name = "F1") -> true
        | _ -> false)
  in

  check bool "Has identity clause" true has_id;
  check bool "Has Invert clause" true has_inv;
  check bool "Found both clause types" true (has_id && has_inv)

let test_10_way_compose () =
  let composition_pairs =
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
  let want =
    Hash_set.of_list
      (module String)
      (List.map composition_pairs ~f:(fun (l, r) ->
           sprintf "Compose(%s,%s)" l r))
  in
  let key_of (cand : BaseLogic.t) =
    match cand.definition with
    | BaseLogic.Clause.Compose (g, h) ->
      Some (sprintf "Compose(%s,%s)" g.name h.name)
    | _ -> None
  in
  let phi (cand : BaseLogic.t) =
    match key_of cand with Some k -> Hash_set.mem want k | None -> false
  in
  let progs = BaseSynthesizer.synth phi in
  let got =
    Hash_set.of_list (module String) (List.filter_map progs ~f:key_of)
  in
  check int "Found all 10 composition patterns" 10 (Hash_set.length got);
  List.iter composition_pairs ~f:(fun (l, r) ->
      let k = sprintf "Compose(%s,%s)" l r in
      check bool ("Contains " ^ k) true (Hash_set.mem got k))

let test_join () =
  let open BaseLogic in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Join (f, g, _) -> String.(f.name = "F0" && g.name = "F1")
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found at least one join" true (not (List.is_empty progs));
  let join_prog =
    List.find_exn progs ~f:(fun p ->
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
    (not (List.is_empty progs));
  let join_prog =
    List.find_exn progs ~f:(fun p ->
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
      (not (List.is_empty progs))
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
      (not (List.is_empty progs))
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
      (not (List.is_empty progs))
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
    (not (List.is_empty progs));
  let multi_join_prog =
    List.find_exn progs ~f:(fun p ->
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
  check bool "Found multiple synthesis options" true (List.length progs >= 2);
  let clause_types =
    List.map progs ~f:(fun p ->
        match p.definition with
        | Clause.Id _ -> "Id"
        | Clause.Invert _ -> "Invert"
        | Clause.MapOut _ -> "MapOut"
        | Clause.MapIn _ -> "MapIn"
        | _ -> "Other")
    |> Set.of_list (module String)
  in
  check bool "Has identity" true (Set.mem clause_types "Id");
  check bool "Has Invert" true (Set.mem clause_types "Invert")
