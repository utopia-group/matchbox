open Core
open Stijl
module Time = Time_ns

let generate_classbench_rules count =
  let temp_file = sprintf "/tmp/cb_rules_%d.txt" count in
  let command =
    sprintf
      "cd /tmp/classbench-ng && ./classbench generate of seeds/of1_seed \
       --count=%d > %s"
      count temp_file
  in
  let exit_code = Caml_unix.system command in
  match exit_code with
  | Caml_unix.WEXITED 0 ->
    let rules = In_channel.read_lines temp_file in
    let _ = Caml_unix.unlink temp_file in
    List.filter rules ~f:(fun line -> not (String.is_empty (String.strip line)))
  | _ ->
    eprintf "ClassBench generation failed\n";
    []

let rules_to_mat rule_strings =
  List.fold rule_strings ~init:[] ~f:(fun acc rule_str ->
      try
        let parsed_rules = ClassBenchParser.parse_from_string rule_str in
        parsed_rules @ acc
      with exn ->
        eprintf "Parse error for rule %s: %s\n" rule_str (Exn.to_string exn);
        acc)

(* Initial configuration populating the ACL table *)
let create_initial_config acl_rules =
  let acl_symbol = AclTranslation.acl.name in
  BaseLogic.Config.
    {
      symbols = String.Set.of_list [acl_symbol];
      cfg = Map.singleton (module String) acl_symbol acl_rules;
    }

let timed_translate acl_rules =
  let initial_config = create_initial_config acl_rules in
  let start_time = Time.now () in
  let step_results, _ =
    BaseInterpreter.eval_program initial_config AclTranslation.acl_translation
  in
  let end_time = Time.now () in
  let runtime = Time.diff end_time start_time in
  let runtime_ms = Time.Span.to_ms runtime in
  let total_mat_size =
    List.fold step_results ~init:0 ~f:(fun acc (_, mat) ->
        acc + List.length mat)
  in
  (runtime_ms, total_mat_size, step_results)

let eval () =
  let rule_counts = [50; 100; 200; 500; 1000] in

  let eval_one count =
    printf "\nEvaluating with %d rules\n%!" count;
    let rule_strings = generate_classbench_rules count in
    let acl_rules = rules_to_mat rule_strings in
    let actual_rule_count = List.length acl_rules in
    printf "Generated %d actual ACL rules from %d rule strings\n%!"
      actual_rule_count count;
    if actual_rule_count > 0 then (
      (* Run translation multiple times for stable timing *)
      let results =
        List.map [1; 2; 3] ~f:(fun _ -> timed_translate acl_rules)
      in
      let runtimes = List.map results ~f:(fun (runtime, _, _) -> runtime) in
      let mat_sizes = List.map results ~f:(fun (_, size, _) -> size) in
      let avg_runtime =
        List.fold runtimes ~init:0.0 ~f:( +. )
        /. Float.of_int (List.length runtimes)
      in
      let avg_mat_size =
        List.fold mat_sizes ~init:0 ~f:( + ) / List.length mat_sizes
      in
      printf
        "Summary:\n\
        \  Input: %d rules\n\
        \  Runtime: %.3f ms\n\
        \  Total output: %d rules\n\
         %!"
        actual_rule_count avg_runtime avg_mat_size;
      List.iter
        (Tuple3.get3 (List.hd_exn results))
        ~f:(fun (step_name, table) ->
          printf "%s: %d rules\n%!" step_name (List.length table));

      Some (actual_rule_count, avg_runtime, avg_mat_size))
    else (
      printf "Skipping - no valid rules generated\n%!";
      None)
  in

  let result_options = List.map rule_counts ~f:eval_one in
  List.filter_map result_options ~f:(fun x -> x)

let write_to_csv results =
  let csv_content =
    String.concat ~sep:"\n"
      ("count,runtime,mat_size"
      :: List.map results ~f:(fun (count, runtime, size) ->
             sprintf "%d,%.6f,%d" count runtime size))
  in
  Out_channel.write_all "eval_acl_results.csv" ~data:csv_content;
  printf "\nResults written to eval_acl_results.csv\n%!"

let () = () |> eval |> write_to_csv
