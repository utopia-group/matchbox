open Core
open Stijl
open Alcotest

let f i = BaseLogic.Symbol.make (sprintf "F%d" i) [] 0

let mk_new_logic defined definition =
  BaseLogic.SurfaceLogic.{defined; definition}

let test_id () =
  let open BaseLogic in
  let target = f 2 in
  let phi (cand : SurfaceLogic.t) =
    match cand.definition with
    | TransformExpr.TableSymbol symbol ->
      Symbol.(symbol = target && cand.defined = target)
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform phi in
  check bool "Found at least one Id(F2)" true (not (List.is_empty progs));
  let identity_prog =
    List.find_exn progs ~f:(fun p ->
        match p.definition with
        | TransformExpr.TableSymbol _ -> true
        | _ -> false)
  in
  match identity_prog with
  | {defined; definition = TransformExpr.TableSymbol symbol} ->
    check string "Defined is F2" "F2" defined.name;
    check string "TableSymbol is F2" "F2" symbol.name
  | _ -> fail "Expected TransformExpr.TableSymbol F2"

let test_compose () =
  let open BaseLogic in
  let phi (cand : SurfaceLogic.t) =
    match cand.definition with
    | TransformExpr.Compose
        (TransformExpr.TableSymbol g, TransformExpr.TableSymbol h) ->
      String.(g.name = "F0" && h.name = "F1" && cand.defined.name = "F2")
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform phi in
  check bool "Found at least one composition" true (not (List.is_empty progs));
  let compose_prog =
    List.find_exn progs ~f:(fun p ->
        match p.definition with
        | TransformExpr.Compose
            (TransformExpr.TableSymbol g, TransformExpr.TableSymbol h) ->
          String.(g.name = "F0" && h.name = "F1" && p.defined.name = "F2")
        | _ -> false)
  in
  match compose_prog.definition with
  | TransformExpr.Compose
      (TransformExpr.TableSymbol g, TransformExpr.TableSymbol h) ->
    check string "Defined is F2" "F2" compose_prog.defined.name;
    check string "Compose left is F0" "F0" g.name;
    check string "Compose right is F1" "F1" h.name
  | _ -> fail "Expected TransformExpr.Compose(TableSymbol F0, TableSymbol F1)"

let test_inverse () =
  let open BaseLogic in
  let target = f 3 in
  let phi (cand : SurfaceLogic.t) =
    match cand.definition with
    | TransformExpr.Invert (TransformExpr.TableSymbol symbol) ->
      String.(symbol.name = target.name) && Symbol.(cand.defined = target)
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform phi in
  check bool "Found at least one Invert(F3)" true (not (List.is_empty progs));
  let inv_prog =
    List.find_exn progs ~f:(fun p ->
        match p.definition with TransformExpr.Invert _ -> true | _ -> false)
  in
  match inv_prog with
  | {
   defined;
   definition = TransformExpr.Invert (TransformExpr.TableSymbol symbol);
  } ->
    check string "Defined is F3" "F3" defined.name;
    check string "Invert table symbol is F3" "F3" symbol.name
  | _ -> fail "Expected TransformExpr.Invert (TableSymbol F3)"

let test_multiple_clause_kinds () =
  let open BaseLogic in
  let phi (cand : SurfaceLogic.t) =
    match cand.definition with
    | TransformExpr.TableSymbol symbol
      when String.(symbol.name = "F0" && cand.defined.name = "F0") ->
      true
    | TransformExpr.Invert (TransformExpr.TableSymbol symbol)
      when String.(symbol.name = "F1" && cand.defined.name = "F1") ->
      true
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform phi in

  let has_table_symbol =
    List.exists progs ~f:(fun p ->
        match p.definition with
        | TransformExpr.TableSymbol symbol when String.(symbol.name = "F0") ->
          true
        | _ -> false)
  in
  let has_inverse =
    List.exists progs ~f:(fun p ->
        match p.definition with
        | TransformExpr.Invert (TransformExpr.TableSymbol symbol)
          when String.(symbol.name = "F1") ->
          true
        | _ -> false)
  in
  check bool "Has table symbol" true has_table_symbol;
  check bool "Has inverse" true has_inverse;
  check bool "Found both transformation types" true
    (has_table_symbol && has_inverse)

let test_10_way_compose () =
  let open BaseLogic in
  let phi (cand : SurfaceLogic.t) =
    match cand.definition with
    | TransformExpr.Compose
        (TransformExpr.TableSymbol _, TransformExpr.TableSymbol _) ->
      true
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform ~max_depth:3 phi in
  check bool "Found composition assignments" true (List.length progs >= 1);
  let found_compose =
    List.exists progs ~f:(fun p ->
        match p.definition with
        | TransformExpr.Compose
            (TransformExpr.TableSymbol _, TransformExpr.TableSymbol _) ->
          true
        | _ -> false)
  in
  check bool "Contains composition" true found_compose

let test_join () =
  let open BaseLogic in
  let phi (cand : SurfaceLogic.t) =
    match cand.definition with
    | TransformExpr.Join
        (TransformExpr.TableSymbol f, TransformExpr.TableSymbol g, _) ->
      String.(f.name = "F0" && g.name = "F1" && cand.defined.name = "F0")
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform phi in
  check bool "Found at least one join" true (not (List.is_empty progs));
  let join_prog =
    List.find_exn progs ~f:(fun p ->
        match p.definition with TransformExpr.Join _ -> true | _ -> false)
  in
  match join_prog.definition with
  | TransformExpr.Join
      (TransformExpr.TableSymbol f, TransformExpr.TableSymbol g, _) ->
    check string "Defined is F0" "F0" join_prog.defined.name;
    check string "Join left is F0" "F0" f.name;
    check string "Join right is F1" "F1" g.name
  | _ -> fail "Expected TransformExpr.Join(TableSymbol F0, TableSymbol F1, [])"

let test_synthesis_variety () =
  let open BaseLogic in
  let target = f 0 in
  let phi (cand : SurfaceLogic.t) =
    Symbol.(cand.defined = target)
    &&
    match cand.definition with
    | TransformExpr.TableSymbol _ -> true
    | TransformExpr.Invert _ -> true
    | _ -> false
  in
  let progs = SurfaceSynthesizer.synth_transform phi in
  check bool "Found multiple synthesis options" true (List.length progs > 1);
  let has_table_symbol =
    List.exists progs ~f:(fun p ->
        match p.definition with
        | TransformExpr.TableSymbol _ -> true
        | _ -> false)
  in
  let has_inverse =
    List.exists progs ~f:(fun p ->
        match p.definition with TransformExpr.Invert _ -> true | _ -> false)
  in
  check bool "Has table symbol" true has_table_symbol;
  check bool "Has inverse" true has_inverse
