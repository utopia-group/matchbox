open Core
open Alcotest
open Matchbox
open Semantics

let mk_symbol name ins out = BaseLogic.Symbol.make name ins out

let mk_test_config symbol rows =
  let prov_rows =
    List.mapi rows ~f:(fun i row ->
        {BaseLogic.ProvRow.loc = (symbol, i); row; prov = Some [(symbol, i)]})
  in
  BaseLogic.
    {
      Config.symbols = [symbol];
      cfg =
        Map.singleton
          (module String)
          symbol.name
          {
            ProvTable.name = symbol.name;
            ins = symbol.ins;
            out = symbol.out;
            idgen = IdGen.init ();
            rows = prov_rows;
          };
    }

let mk_match_action_rule ~matches ~action_name ~action_data =
  {
    MatchAction.matches = Map.of_alist_exn (module String) matches;
    action =
      Action.make action_name (Map.of_alist_exn (module String) action_data);
  }

let test_filter () =
  let symbol = mk_symbol "complex_table" [32; 16; 8] 32 in

  let row1 =
    mk_match_action_rule
      ~matches:
        [
          ("dst", Match.exact (Bit.Vector.of_int ~width:32 42));
          ("src", Match.exact (Bit.Vector.of_int ~width:16 100));
        ]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let row2 =
    mk_match_action_rule
      ~matches:
        [
          ("dst", Match.exact (Bit.Vector.of_int ~width:32 43));
          ("src", Match.exact (Bit.Vector.of_int ~width:16 100));
        ]
      ~action_name:"drop" ~action_data:[]
  in
  let row3 =
    mk_match_action_rule
      ~matches:
        [
          ("dst", Match.exact (Bit.Vector.of_int ~width:32 42));
          ("src", Match.exact (Bit.Vector.of_int ~width:16 200));
        ]
      ~action_name:"mirror"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 2)]
  in
  let row4 =
    mk_match_action_rule
      ~matches:
        [
          ("dst", Match.exact (Bit.Vector.of_int ~width:32 44));
          ("proto", Match.exact (Bit.Vector.of_int ~width:8 6));
        ]
      ~action_name:"route"
      ~action_data:[("next_hop", Bit.Vector.of_int ~width:32 192)]
  in
  let row5 =
    mk_match_action_rule
      ~matches:
        [
          ( "dst",
            Match.Ternary
              (Trit.Vector.of_bitmask
                 (Bit.Vector.of_int ~width:32 0x2A000000)
                 (Bit.Vector.of_int ~width:32 0xFF000000)) );
        ]
      ~action_name:"default" ~action_data:[]
  in
  let config = mk_test_config symbol [row1; row2; row3; row4; row5] in

  let filter_exact =
    String.Map.singleton "dst" (Match.exact (Bit.Vector.of_int ~width:32 42))
  in
  let transform_exact =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_exact)
  in
  let result_exact = SurfaceInterpreter.eval transform_exact config in
  check int "Exact filter matches correct rows" 2 (List.length result_exact);
  let actions =
    List.map result_exact ~f:(fun row -> Action.get_name row.action)
    |> List.sort ~compare:String.compare
  in
  check (list string) "Exact filter keeps correct actions" ["fwd"; "mirror"]
    actions;

  let filter_multi =
    String.Map.of_alist_exn
      [
        ("dst", Match.exact (Bit.Vector.of_int ~width:32 42));
        ("src", Match.exact (Bit.Vector.of_int ~width:16 100));
      ]
  in
  let transform_multi =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_multi)
  in
  let result_multi = SurfaceInterpreter.eval transform_multi config in
  check int "Multi-field filter matches one row" 1 (List.length result_multi);
  check string "Multi-field filter keeps fwd action" "fwd"
    (Action.get_name (List.hd_exn result_multi).action);

  let filter_proto =
    String.Map.singleton "proto" (Match.exact (Bit.Vector.of_int ~width:8 6))
  in
  let transform_proto =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_proto)
  in
  let result_proto = SurfaceInterpreter.eval transform_proto config in
  check int "Protocol filter matches correct row" 1 (List.length result_proto);
  check string "Protocol filter keeps route action" "route"
    (Action.get_name (List.hd_exn result_proto).action);

  let filter_ternary =
    String.Map.singleton "dst"
      (Match.Ternary
         (Trit.Vector.of_bitmask
            (Bit.Vector.of_int ~width:32 0x2A000000)
            (Bit.Vector.of_int ~width:32 0xFF000000)))
  in
  let transform_ternary =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_ternary)
  in
  let result_ternary = SurfaceInterpreter.eval transform_ternary config in
  check int "Ternary filter matches correct row" 1 (List.length result_ternary);
  check string "Ternary filter keeps default action" "default"
    (Action.get_name (List.hd_exn result_ternary).action);

  let filter_empty =
    String.Map.singleton "dst" (Match.exact (Bit.Vector.of_int ~width:32 999))
  in
  let transform_empty =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_empty)
  in
  let result_empty = SurfaceInterpreter.eval transform_empty config in
  check int "Non-matching filter returns empty" 0 (List.length result_empty);

  let filter_nonexistent =
    String.Map.singleton "nonexistent"
      (Match.exact (Bit.Vector.of_int ~width:32 42))
  in
  let transform_nonexistent =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_nonexistent)
  in
  let result_nonexistent =
    SurfaceInterpreter.eval transform_nonexistent config
  in
  check int "Filter on non-existent field returns empty" 0
    (List.length result_nonexistent);

  let inner_filter =
    String.Map.singleton "dst" (Match.exact (Bit.Vector.of_int ~width:32 42))
  in
  let inner_transform =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, inner_filter)
  in
  let outer_filter =
    String.Map.singleton "src" (Match.exact (Bit.Vector.of_int ~width:16 100))
  in
  let outer_transform =
    BaseLogic.TransformExpr.Filter (inner_transform, outer_filter)
  in
  let result_composed = SurfaceInterpreter.eval outer_transform config in
  check int "Composed filter matches one row" 1 (List.length result_composed);
  check string "Composed filter keeps fwd action" "fwd"
    (Action.get_name (List.hd_exn result_composed).action);

  let conflicting_filter =
    String.Map.singleton "dst" (Match.exact (Bit.Vector.of_int ~width:32 44))
  in
  let transform_conflict =
    BaseLogic.TransformExpr.Filter
      ( BaseLogic.TransformExpr.Filter
          (BaseLogic.TransformExpr.TableSymbol symbol, filter_exact),
        conflicting_filter )
  in
  let result_conflict = SurfaceInterpreter.eval transform_conflict config in
  check int "Conflicting composed filter returns empty" 0
    (List.length result_conflict)

let test_transform_table_symbol () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let config = mk_test_config symbol [row1] in
  let transform_expr = BaseLogic.TransformExpr.TableSymbol symbol in
  let result = SurfaceInterpreter.eval transform_expr config in
  check int "Table symbol returns original table" 1 (List.length result);
  let result_row = List.hd_exn result in
  check string "Action name preserved" "fwd" (Action.get_name result_row.action)

let test_transform_compose () =
  let symbol1 = mk_symbol "table1" [32] 32 in
  let symbol2 = mk_symbol "table2" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"intermediate"
      ~action_data:[("next_dst", Bit.Vector.of_int ~width:32 100)]
  in
  let row2 =
    mk_match_action_rule
      ~matches:[("next_dst", Match.exact (Bit.Vector.of_int ~width:32 100))]
      ~action_name:"final"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 5)]
  in
  let config1 = mk_test_config symbol1 [row1] in
  let config2 = mk_test_config symbol2 [row2] in
  let config =
    {
      BaseLogic.Config.symbols = [symbol1; symbol2];
      cfg =
        Map.of_alist_exn
          (module String)
          [
            (symbol1.name, BaseLogic.Config.find_exn config1 symbol1);
            (symbol2.name, BaseLogic.Config.find_exn config2 symbol2);
          ];
    }
  in
  let transform_expr =
    BaseLogic.TransformExpr.Compose
      ( BaseLogic.TransformExpr.TableSymbol symbol1,
        BaseLogic.TransformExpr.TableSymbol symbol2 )
  in
  let result = SurfaceInterpreter.eval transform_expr config in
  check int "Compose produces one result row" 1 (List.length result);
  let result_row = List.hd_exn result in
  check string "Final action from second table" "final"
    (Action.get_name result_row.action)

let test_transform_join () =
  let symbol1 = mk_symbol "table1" [32] 32 in
  let symbol2 = mk_symbol "table2" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let row2 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"tag"
      ~action_data:[("vlan", Bit.Vector.of_int ~width:16 100)]
  in
  let config1 = mk_test_config symbol1 [row1] in
  let config2 = mk_test_config symbol2 [row2] in
  let config =
    {
      BaseLogic.Config.symbols = [symbol1; symbol2];
      cfg =
        Map.of_alist_exn
          (module String)
          [
            (symbol1.name, BaseLogic.Config.find_exn config1 symbol1);
            (symbol2.name, BaseLogic.Config.find_exn config2 symbol2);
          ];
    }
  in
  let alignment = [(("fwd", "tag"), "fwd_tagged")] in
  let transform_expr =
    BaseLogic.TransformExpr.Join
      ( BaseLogic.TransformExpr.TableSymbol symbol1,
        BaseLogic.TransformExpr.TableSymbol symbol2,
        alignment )
  in
  let result = SurfaceInterpreter.eval transform_expr config in
  check int "Join with matching rows produces one merged row" 1
    (List.length result);
  let result_row = List.hd_exn result in
  check string "Join creates merged action" "fwd_tagged"
    (Action.get_name result_row.action)

let test_transform_project () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:
        [
          ("dst", Match.exact (Bit.Vector.of_int ~width:32 42));
          ("src", Match.exact (Bit.Vector.of_int ~width:32 100));
        ]
      ~action_name:"fwd"
      ~action_data:
        [
          ("port", Bit.Vector.of_int ~width:8 1);
          ("vlan", Bit.Vector.of_int ~width:16 200);
        ]
  in
  let config = mk_test_config symbol [row1] in
  let transform_expr =
    BaseLogic.TransformExpr.Project
      (BaseLogic.TransformExpr.TableSymbol symbol, ["dst"])
  in
  let result = SurfaceInterpreter.eval transform_expr config in
  check int "Project preserves number of rows" 1 (List.length result);
  let result_row = List.hd_exn result in
  let matches = MatchAction.get_matches result_row in
  check bool "Project keeps specified fields" true (Map.mem matches "dst");
  check bool "Project keeps specified fields" true (Map.mem matches "dst");
  check bool "Project removes unspecified fields" false (Map.mem matches "src")

let test_transform_invert () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let config = mk_test_config symbol [row1] in
  let transform_expr =
    BaseLogic.TransformExpr.Invert (BaseLogic.TransformExpr.TableSymbol symbol)
  in
  let result = SurfaceInterpreter.eval transform_expr config in
  check bool "Invert produces result" true (List.length result > 0);
  let result_row = List.hd_exn result in
  let matches = MatchAction.get_matches result_row in
  let action_data = Action.get_data result_row.action in
  check bool "Invert creates matches from action data" true
    (Map.mem matches "port");
  check bool "Invert creates action data from matches" true
    (Map.mem action_data "dst")

let test_bitvec_expressions () =
  let symbol = mk_symbol "bv_test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("src", Match.exact (Bit.Vector.of_int ~width:32 10))]
      ~action_name:"calc"
      ~action_data:
        [
          ("val1", Bit.Vector.of_int ~width:32 5);
          ("val2", Bit.Vector.of_int ~width:32 7);
        ]
  in
  let config = mk_test_config symbol [row1] in

  let add_assignment = [("result", Bit.Vector.of_int ~width:32 12)] in
  let emit_expr =
    BaseLogic.TransformExpr.WriteData
      (BaseLogic.TransformExpr.TableSymbol symbol, add_assignment)
  in
  let result = SurfaceInterpreter.eval emit_expr config in
  let result_row = List.hd_exn result in
  let result_val = Map.find_exn (Action.get_data result_row.action) "result" in
  check int "BVAdd works correctly" 12 (Bit.Vector.to_int result_val);

  let and_assignment = [("and_result", Bit.Vector.of_int ~width:32 1)] in
  let and_expr =
    BaseLogic.TransformExpr.WriteData
      (BaseLogic.TransformExpr.TableSymbol symbol, and_assignment)
  in
  let and_result = SurfaceInterpreter.eval and_expr config in
  let and_row = List.hd_exn and_result in
  let and_val = Map.find_exn (Action.get_data and_row.action) "and_result" in
  check int "BVAnd works correctly" 1 (Bit.Vector.to_int and_val)

let test_transform_to_clause_encoding () =
  let symbol = mk_symbol "filter_test" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd" ~action_data:[]
  in
  let row2 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 43))]
      ~action_name:"drop" ~action_data:[]
  in
  let config = mk_test_config symbol [row1; row2] in

  let filter_matches =
    Map.singleton
      (module String)
      "dst"
      (Match.exact (Bit.Vector.of_int ~width:32 42))
  in
  let transform_filter =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_matches)
  in
  let transform_result = SurfaceInterpreter.eval transform_filter config in

  let output_symbol = mk_symbol "output" [32] 32 in
  let mid_symbol_filter = mk_symbol "F2" [32] 32 in
  let mid_symbol_project = mk_symbol "F1" [32] 32 in
  let filter_steps =
    BaseLogic.filter symbol filter_matches mid_symbol_filter output_symbol
  in
  let project_steps =
    BaseLogic.project symbol ["dst"; "src"] mid_symbol_project output_symbol
  in
  let table_steps = BaseLogic.table_symbol symbol output_symbol in

  check int "TransformExpr.Filter works" 1 (List.length transform_result);
  check string "Filters to correct action" "fwd"
    (Action.get_name (List.hd_exn transform_result).action);

  check int "Filter encoding creates two steps" 2 (List.length filter_steps);
  check int "Project encoding creates two steps" 2 (List.length project_steps);
  check int "Table symbol creates single step" 1 (List.length table_steps);

  let project_intermediate = (List.hd_exn project_steps).defined in
  check string "Project uses hardcoded F1 intermediate" "F1"
    project_intermediate.name;

  let filter_intermediate = (List.hd_exn filter_steps).defined in
  check string "Filter uses hardcoded F2 intermediate" "F2"
    filter_intermediate.name

let test_filter_action_constraint () =
  let symbol = mk_symbol "action_filter_test" [32] 32 in

  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("dst", Bit.Vector.of_int ~width:32 42)]
  in

  let row2 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("dst", Bit.Vector.of_int ~width:32 999)]
  in

  let config = mk_test_config symbol [row1; row2] in

  let filter_matches =
    Map.singleton
      (module String)
      "dst"
      (Match.exact (Bit.Vector.of_int ~width:32 42))
  in

  let transform_filter =
    BaseLogic.TransformExpr.Filter
      (BaseLogic.TransformExpr.TableSymbol symbol, filter_matches)
  in

  let result = SurfaceInterpreter.eval transform_filter config in
  let result_row = List.hd_exn result in
  let action_data = Action.get_data result_row.action in
  let dst_value = Map.find_exn action_data "dst" in
  check int "Action data matches filter constraint" 42
    (Bit.Vector.to_int dst_value);

  check int "Filter with action constraint" 1 (List.length result)
