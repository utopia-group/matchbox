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
    | Clause.Compose (g, h) ->
      String.(g.name = "F0" && h.name = "F1" && cand.defined.name = "F2")
    | _ -> false
  in
  let progs = BaseSynthesizer.synth phi in
  check bool "Found at least one composition" true (not (List.is_empty progs));
  let compose_prog =
    List.find_exn progs ~f:(fun p ->
        match p.definition with
        | Clause.Compose (g, h) ->
          String.(g.name = "F0" && h.name = "F1" && p.defined.name = "F2")
        | _ -> false)
  in
  match compose_prog.definition with
  | Clause.Compose (g, h) ->
    check string "Defined is F2" "F2" compose_prog.defined.name;
    check string "Compose left is F0" "F0" g.name;
    check string "Compose right is F1" "F1" h.name
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
    | Clause.Id f' when String.(f'.name = "F0" && cand.defined.name = "F0") ->
      true
    | Clause.Invert f' when String.(f'.name = "F1" && cand.defined.name = "F1")
      ->
      true
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
  let assignments =
    [
      ("F2", "F0", "F1");
      ("F4", "F2", "F3");
      ("F6", "F4", "F5");
      ("F8", "F6", "F7");
      ("F10", "F8", "F9");
      ("F12", "F10", "F11");
      ("F14", "F12", "F13");
      ("F16", "F14", "F15");
      ("F18", "F16", "F17");
      ("F20", "F18", "F19");
    ]
  in
  let want =
    Hash_set.of_list
      (module String)
      (List.map assignments ~f:(fun (d, l, r) ->
           sprintf "%s := Compose(%s,%s)" d l r))
  in
  let key_of (cand : BaseLogic.t) =
    match cand.definition with
    | BaseLogic.Clause.Compose (g, h) ->
      Some (sprintf "%s := Compose(%s,%s)" cand.defined.name g.name h.name)
    | _ -> None
  in
  let phi (cand : BaseLogic.t) =
    match key_of cand with Some k -> Hash_set.mem want k | None -> false
  in
  let progs = BaseSynthesizer.synth phi in
  let got =
    Hash_set.of_list (module String) (List.filter_map progs ~f:key_of)
  in
  check int "Found all 10 assignments" 10 (Hash_set.length got);
  List.iter assignments ~f:(fun (d, l, r) ->
      let k = sprintf "%s := Compose(%s,%s)" d l r in
      check bool ("Contains " ^ k) true (Hash_set.mem got k))

let test_join () =
  let open BaseLogic in
  let phi (cand : t) =
    match cand.definition with
    | Clause.Join (f, g, _) ->
      String.(f.name = "F0" && g.name = "F1" && cand.defined.name = "F0")
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
    check string "Defined is F0" "F0" join_prog.defined.name;
    check string "Join left is F0" "F0" f.name;
    check string "Join right is F1" "F1" g.name
  | _ -> fail "Expected Clause.Join(F0,F1,[])"

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
