open Core
open Alcotest
open Stijl
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

let test_empty_table () =
  let symbol = mk_symbol "empty_table" [32] 32 in
  let config = mk_test_config symbol [] in
  let clause = BaseLogic.Clause.Id symbol in
  let result = BaseInterpreter.eval clause config in
  check int "Empty table returns empty result" 0 (List.length result)

let test_unrelated_clause () =
  let symbol_target = mk_symbol "target_table" [32] 32 in
  let symbol_other = mk_symbol "other_table" [32] 32 in
  let test_row =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let config = mk_test_config symbol_target [test_row] in
  let clause = BaseLogic.Clause.Id symbol_other in
  let result = BaseInterpreter.eval clause config in
  check int "Unrelated clause returns empty result" 0 (List.length result)

let test_id () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let row2 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 43))]
      ~action_name:"drop" ~action_data:[]
  in
  let config = mk_test_config symbol [row1; row2] in
  let clause = BaseLogic.Clause.Id symbol in
  let result = BaseInterpreter.eval clause config in
  check int "Rows preserved" 2 (List.length result);
  let actions = List.map result ~f:(fun row -> Action.get_name row.action) in
  check bool "Contains fwd action" true
    (List.mem actions "fwd" ~equal:String.equal);
  check bool "Contains drop action" true
    (List.mem actions "drop" ~equal:String.equal)

let test_join () =
  let symbol_f = mk_symbol "table_f" [32] 32 in
  let symbol_g = mk_symbol "table_g" [32] 32 in
  let row_f =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let row_g =
    mk_match_action_rule (* Same match so join happens *)
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"tag_vlan"
      ~action_data:[("vlan_id", Bit.Vector.of_int ~width:16 100)]
  in
  let config_f = mk_test_config symbol_f [row_f] in
  let config_g = mk_test_config symbol_g [row_g] in
  let config =
    {
      BaseLogic.Config.symbols = [symbol_f; symbol_g];
      cfg =
        Map.of_alist_exn
          (module String)
          [
            (symbol_f.name, BaseLogic.Config.find_exn config_f symbol_f);
            (symbol_g.name, BaseLogic.Config.find_exn config_g symbol_g);
          ];
    }
  in
  let merge = [(("fwd", "tag_vlan"), "fwd_with_vlan")] in
  let clause = BaseLogic.Clause.Join (symbol_f, symbol_g, merge) in
  let result = BaseInterpreter.eval clause config in
  check int "Join with matching rows produces one merged row" 1
    (List.length result);
  let result_row = List.hd_exn result in
  check string "Join creates merged action" "fwd_with_vlan"
    (Action.get_name result_row.action)

let test_inverse () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let test_row =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let config = mk_test_config symbol [test_row] in
  let clause = BaseLogic.Clause.Inverse symbol in
  let result = BaseInterpreter.eval clause config in
  check bool "Inverse clause produces result" true (List.length result > 0);
  let result_row = List.hd_exn result in
  let new_matches = MatchAction.get_matches result_row in
  check bool "Inverse creates matches from action data" true
    (Map.mem new_matches "port");
  let new_action_data = result_row.action.args in
  check bool "Inverse creates action data from matches" true
    (Map.mem new_action_data "dst")

let test_mapout_project () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:
        [
          ("port", Bit.Vector.of_int ~width:8 1);
          ("vlan", Bit.Vector.of_int ~width:16 100);
          ("priority", Bit.Vector.of_int ~width:8 5);
        ]
  in
  let row2 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 43))]
      ~action_name:"drop"
      ~action_data:
        [
          ("port", Bit.Vector.of_int ~width:8 2);
          ("vlan", Bit.Vector.of_int ~width:16 200);
          ("priority", Bit.Vector.of_int ~width:8 3);
        ]
  in
  let config = mk_test_config symbol [row1; row2] in
  let clause =
    BaseLogic.Clause.MapOut
      (symbol, BaseLogic.ActionTfx.Project ["port"; "vlan"])
  in
  let result = BaseInterpreter.eval clause config in
  check int "MapOut Project returns same number of rows" 2 (List.length result);
  let result_row1 = List.hd_exn result in
  check string "MapOut Project preserves first action name" "fwd"
    (Action.get_name result_row1.action);
  check int "MapOut Project keeps only specified params" 2
    (Map.length result_row1.action.args);
  check bool "MapOut Project keeps port" true
    (Map.mem result_row1.action.args "port");
  check bool "MapOut Project keeps vlan" true
    (Map.mem result_row1.action.args "vlan");
  check bool "MapOut Project removes priority" false
    (Map.mem result_row1.action.args "priority");
  let result_row2 = List.nth_exn result 1 in
  check string "MapOut Project preserves second action name" "drop"
    (Action.get_name result_row2.action)

let test_mapout_setto () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let row1 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"forward"
      ~action_data:
        [
          ("base_port", Bit.Vector.of_int ~width:8 5);
          ("priority", Bit.Vector.of_int ~width:8 3);
          ("bandwidth", Bit.Vector.of_int ~width:16 1000);
        ]
  in
  let row2 =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 43))]
      ~action_name:"load_balance"
      ~action_data:
        [
          ("base_port", Bit.Vector.of_int ~width:8 10);
          ("priority", Bit.Vector.of_int ~width:8 7);
          ("bandwidth", Bit.Vector.of_int ~width:16 2000);
        ]
  in
  let config = mk_test_config symbol [row1; row2] in

  (* Test 1: AddK transformation (adjust port) *)
  let adjusted_port_expr =
    BaseLogic.ActionTfx.AddK
      (BaseLogic.ActionTfx.Var "base_port", Bit.Vector.of_int ~width:8 100)
  in
  let add_clause =
    BaseLogic.Clause.MapOut
      (symbol, BaseLogic.ActionTfx.SetTo ("adjusted_port", adjusted_port_expr))
  in
  let add_result = BaseInterpreter.eval add_clause config in
  check int "MapOut SetTo AddK returns same number of rows" 2
    (List.length add_result);
  let result_row1 = List.hd_exn add_result in
  check string "MapOut SetTo AddK preserves action name" "forward"
    (Action.get_name result_row1.action);
  check int "MapOut SetTo AddK adds one new parameter" 4
    (Map.length result_row1.action.args);
  let adjusted_port1 = Map.find_exn result_row1.action.args "adjusted_port" in
  check int "MapOut SetTo AddK calculates adjusted_port correctly in first row"
    105
    (Bit.Vector.to_int adjusted_port1);
  check bool "MapOut SetTo AddK preserves original base_port" true
    (Map.mem result_row1.action.args "base_port");
  check bool "MapOut SetTo AddK preserves priority" true
    (Map.mem result_row1.action.args "priority");
  check bool "MapOut SetTo AddK preserves bandwidth" true
    (Map.mem result_row1.action.args "bandwidth");
  let result_row2 = List.nth_exn add_result 1 in
  let adjusted_port2 = Map.find_exn result_row2.action.args "adjusted_port" in
  check int "MapOut SetTo AddK calculates adjusted_port correctly in second row"
    110
    (Bit.Vector.to_int adjusted_port2);

  (* Test 2: SubK transformation (reduce bandwidth) *)
  let reduced_bandwidth_expr =
    BaseLogic.ActionTfx.SubK
      (BaseLogic.ActionTfx.Var "bandwidth", Bit.Vector.of_int ~width:16 500)
  in
  let sub_clause =
    BaseLogic.Clause.MapOut
      ( symbol,
        BaseLogic.ActionTfx.SetTo ("reduced_bandwidth", reduced_bandwidth_expr)
      )
  in
  let sub_result = BaseInterpreter.eval sub_clause config in
  let sub_row1 = List.hd_exn sub_result in
  let reduced_bw1 = Map.find_exn sub_row1.action.args "reduced_bandwidth" in
  check int "MapOut SetTo SubK calculates reduced bandwidth in first row" 500
    (Bit.Vector.to_int reduced_bw1);
  let sub_row2 = List.nth_exn sub_result 1 in
  let reduced_bw2 = Map.find_exn sub_row2.action.args "reduced_bandwidth" in
  check int "MapOut SetTo SubK calculates reduced bandwidth in second row" 1500
    (Bit.Vector.to_int reduced_bw2);

  (* Test 3: Data injection (add monitoring flag) *)
  let monitoring_clause =
    BaseLogic.Clause.MapOut
      ( symbol,
        BaseLogic.ActionTfx.SetTo
          ( "monitoring_enabled",
            BaseLogic.ActionTfx.Data (Bit.Vector.of_int ~width:1 1) ) )
  in
  let monitor_result = BaseInterpreter.eval monitoring_clause config in
  let monitor_row = List.hd_exn monitor_result in
  check string "MapOut SetTo Data preserves action name" "forward"
    (Action.get_name monitor_row.action);
  let monitor_flag =
    Map.find_exn monitor_row.action.args "monitoring_enabled"
  in
  check int "MapOut SetTo Data sets static value correctly" 1
    (Bit.Vector.to_int monitor_flag);
  check int "MapOut SetTo Data adds one new parameter" 4
    (Map.length monitor_row.action.args)

let test_mapin_project () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let test_row =
    mk_match_action_rule
      ~matches:
        [
          ("src", Match.exact (Bit.Vector.of_int ~width:32 10));
          ("dst", Match.exact (Bit.Vector.of_int ~width:32 42));
        ]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let config = mk_test_config symbol [test_row] in
  let tfx = BaseLogic.MatchTfx.Project ["dst"] in
  let clause = BaseLogic.Clause.MapIn (symbol, tfx) in
  let result = BaseInterpreter.eval clause config in
  check int "MapIn Project returns same number of rows" 1 (List.length result);
  let result_row = List.hd_exn result in
  check bool "MapIn Project removes non-projected fields" false
    (Map.mem result_row.matches "src");
  check bool "MapIn Project keeps only projected fields" true
    (Map.mem result_row.matches "dst")

let test_mapin_setto () =
  let symbol = mk_symbol "test_table" [32] 32 in
  let test_row =
    mk_match_action_rule
      ~matches:[("dst", Match.exact (Bit.Vector.of_int ~width:32 42))]
      ~action_name:"fwd"
      ~action_data:[("port", Bit.Vector.of_int ~width:8 1)]
  in
  let config = mk_test_config symbol [test_row] in
  let new_match = Match.exact (Bit.Vector.of_int ~width:32 10) in
  let tfx =
    BaseLogic.MatchTfx.SetTo ("src", BaseLogic.MatchTfx.Match new_match)
  in
  let clause = BaseLogic.Clause.MapIn (symbol, tfx) in
  let result = BaseInterpreter.eval clause config in
  check int "MapIn SetTo returns same number of rows" 1 (List.length result);
  let result_row = List.hd_exn result in
  check bool "MapIn SetTo preserves existing fields" true
    (Map.mem result_row.matches "dst");
  check bool "MapIn SetTo adds new field" true
    (Map.mem result_row.matches "src")
