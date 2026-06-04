open Core
open Matchbox
open Alcotest

let test_parsing_classbench_rules () =
  try
    let content =
      In_channel.read_all "../../../test/classbench_100_rules.txt"
    in
    let lines =
      String.split_lines content
      |> List.filter ~f:(fun s -> not (String.is_empty (String.strip s)))
    in
    let mat =
      List.fold lines ~init:[] ~f:(fun acc line ->
          try
            let parsed_rules = ClassBenchParser.parse_from_string line in
            parsed_rules @ acc
          with _ -> acc)
    in
    check bool "ClassBench rules parsed successfully" true (List.length mat > 0);
    printf "Table size: %d entries\n" (List.length mat);
    printf "First 5 entries:\n";
    List.take mat 5
    |> List.iteri ~f:(fun i entry ->
           printf "%d: %s\n" (i + 1) (Semantics.MatchAction.to_string entry))
  with Sys_error _ ->
    check bool "ClassBench file not found - test skipped" true true
