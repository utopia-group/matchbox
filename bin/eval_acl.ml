open Core
open Stijl
open BaseLogic
open Utils

let aws_schema =
  [
    ("ipv4", ["hdr.ipv4.dstAddr"], ["dstAddr"; "port"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
  ]

let azure_schema =
  [
    ("ipv4_fib", ["hdr.ipv4.dstAddr"], ["port"]);
    ("ipv4_rewrite", ["hdr.ipv4.dstAddr"], ["dstAddr"]);
    ("ethernet", ["hdr.ethernet.dstAddr"], ["port"]);
    ( "punt",
      [
        "hdr.ethernet.etherType";
        "hdr.ipv4.isValid()";
        "hdr.ipv4.version";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.ttl";
      ],
      [] );
  ]

let ethernet = Symbol.make "ethernet" [] 0
let ipv4 = Symbol.make "ipv4" [] 0
let punt = Symbol.make "punt" [] 0
let ipv4_fib = Symbol.make "ipv4_fib" [] 0
let ipv4_rewrite = Symbol.make "ipv4_rewrite" [] 0

(* logical.p4 to action_decompose.p4 *)

let ipv4_to_ipv4_fib : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "port" 9])

let ipv4_to_ipv4_rewrite : Clause.t =
  Clause.(id ipv4 |>> Project [Var.make "dstAddr" 48])

let logical_to_action_decompose_tfxs : t list =
  [
    {defined = ipv4_fib; definition = ipv4_to_ipv4_fib};
    {defined = ipv4_rewrite; definition = ipv4_to_ipv4_rewrite};
    {defined = ethernet; definition = Clause.id ethernet};
    {defined = punt; definition = Clause.id punt};
  ]

let () =
  let output_dir = "Pipelines/retargeting" in
  (* (id, output_name, input_file, input_schema, output_schema, translation) *)
  let all_tfxs =
    [
      ( "lo_ad",
        "logical_inserts_1001.csv",
        aws_schema,
        azure_schema,
        logical_to_action_decompose_tfxs );
    ]
  in
  (* Map.iteri
    ~f:(fun ~key:op ~data:cnt -> printf "$%s$ & %d \\\\\n" op cnt)
    (List.fold all_tfxs
       ~init:(Map.empty (module String))
       ~f:(fun acc (_, _, _, _, _, tfxs) ->
         List.fold tfxs ~init:acc ~f:(fun acc (_, t) ->
             Clause.count_components acc t))); *)
  List.iteri all_tfxs
    ~f:(fun _i (_id, input_file, input_schema, output_schema, tfxs) ->
      (* printf "(%d, %d, \"%s\"),\n" (i + 1)
        (List.fold tfxs ~init:0 ~f:(fun acc (_, t) -> acc + Clause.size t))
        id; *)
      let input_file = sprintf "%s/%s" output_dir input_file in
      let output_file = sprintf "%s/%s.csv" output_dir _id in
      let parsed_tables = read_csv_by_table input_file input_schema in
      let start_time = Time_ns.now () in
      let translated_tables = transform_mats tfxs parsed_tables in
      let end_time = Time_ns.now () in
      let elapsed_time_us =
        Time_ns.Span.to_ns (Time_ns.diff end_time start_time) /. 1000.0
      in
      translated_tables
      |> List.concat_map ~f:(fun (table_sym, table) ->
             table_to_csv_lines ~schema:(Some output_schema)
               table_sym.Symbol.name table)
      |> Out_channel.write_lines output_file;
      (* printf "Translating %s completed in %.1f μs\n" name elapsed_time_us) *)
      printf "(\"%s\", %.1f),\n" _id elapsed_time_us)
