[@@@warning "-32-21"]

open Core
open Stijl
open BaseLogic
open Semantics
open Utils

let acl_schema =
  [
    ( "acl",
      [
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.proto";
        "meta.l4_sport";
        "meta.l4_dport";
      ],
      [("allow", []); ("deny", [])] );
  ]

let acl_schema' =
  [
    ( "acl",
      [
        "meta.is_inbound";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "hdr.ipv4.proto";
        "meta.l4_sport";
        "meta.l4_dport";
      ],
      [("allow", []); ("deny", [])] );
  ]

let aws_schema =
  [
    ( "inbound_acl",
      ["hdr.ipv4.srcAddr"; "hdr.ipv4.proto"; "meta.l4_sport"],
      [("allow", []); ("deny", [])] );
    ( "outbound_acl",
      ["hdr.ipv4.dstAddr"; "hdr.ipv4.proto"; "meta.l4_dport"],
      [("allow", []); ("deny", [])] );
  ]

let azure_schema =
  [
    ( "acl",
      [
        "meta.is_inbound";
        "hdr.ipv4.proto";
        "hdr.ipv4.srcAddr";
        "hdr.ipv4.dstAddr";
        "meta.l4_sport";
        "meta.l4_dport";
      ],
      [("allow", []); ("deny", [])] );
  ]

(* acl to aws *)

let acl = Symbol.make "acl" [] 0
let direction = Symbol.make "direction" [] 0
let inbound_acl = Symbol.make "inbound_acl" [] 0
let outbound_acl = Symbol.make "outbound_acl" [] 0

let acl_to_inbound_acl : Clause.t =
  Clause.(
    Project
      [
        Var.make "hdr.ipv4.srcAddr" 32;
        Var.make "hdr.ipv4.proto" 8;
        Var.make "meta.l4_sport" 16;
      ]
    <<| (CubeFilter
           (Map.singleton
              (module String)
              "meta.is_inbound"
              (Semantics.Match.Exact (Bit.Vector.of_int ~width:2 0)))
        <<| id acl))

let acl_to_outbound_acl : Clause.t =
  Clause.(
    Project
      [
        Var.make "hdr.ipv4.dstAddr" 32;
        Var.make "hdr.ipv4.proto" 8;
        Var.make "meta.l4_dport" 16;
      ]
    <<| (CubeFilter
           (Map.singleton
              (module String)
              "meta.is_inbound"
              (Semantics.Match.Exact (Bit.Vector.of_int ~width:2 1)))
        <<| id acl))

let acl_to_aws_tfxs : t list =
  [
    {defined = inbound_acl; definition = acl_to_inbound_acl};
    {defined = outbound_acl; definition = acl_to_outbound_acl};
  ]

(* acl to azure *)

let acl_to_acl : Clause.t =
  Clause.(
    Project
      [
        Var.make "meta.is_inbound" 2;
        Var.make "hdr.ipv4.proto" 8;
        Var.make "hdr.ipv4.srcAddr" 32;
        Var.make "hdr.ipv4.dstAddr" 32;
        Var.make "meta.l4_sport" 16;
        Var.make "meta.l4_dport" 16;
      ]
    <<| id acl)

let acl_to_azure_tfxs : t list = [{defined = acl; definition = acl_to_acl}]

(* acl to google *)

let acl_to_acl' : Clause.t =
  Clause.(
    Project
      [
        Var.make "meta.is_inbound" 2;
        Var.make "hdr.ipv4.proto" 8;
        Var.make "hdr.ipv4.srcAddr" 32;
        Var.make "hdr.ipv4.dstAddr" 32;
        Var.make "meta.l4_sport" 16;
        Var.make "meta.l4_dport" 16;
      ]
    <<| id acl)

let acl_to_google_tfxs : t list = [{defined = acl; definition = acl_to_acl'}]

(* aws to azure *)

let inbound_outbound_to_acl : Clause.t =
  Clause.(
    WildCard (Var.make "meta.l4_dport" 16)
    <<| (WildCard (Var.make "hdr.ipv4.dstAddr" 32)
        <<| (SetTo
               (Var.make "meta.is_inbound" 2, Gpl.Expr.BV (Bigint.of_int 0, 2))
            <<| id inbound_acl))
    |> (WildCard (Var.make "meta.l4_sport" 16)
       <<| (WildCard (Var.make "hdr.ipv4.srcAddr" 32)
           <<| (SetTo
                  ( Var.make "meta.is_inbound" 2,
                    Gpl.Expr.BV (Bigint.of_int 1, 2) )
               <<| id outbound_acl))))

let aws_to_azure_tfxs : t list =
  [{defined = acl; definition = inbound_outbound_to_acl}]

(* azure to aws *)

let azure_to_aws_tfxs : t list =
  [
    {defined = inbound_acl; definition = acl_to_inbound_acl};
    {defined = outbound_acl; definition = acl_to_outbound_acl};
  ]

let () =
  Random.init 42;
  let output_dir = "Pipelines/acl" in
  let classbench_config =
    sprintf "%s/_classbench_acl_inserts_1000.csv" output_dir
  in
  let normalized_config =
    sprintf "%s/classbench_acl_inserts_1000.csv" output_dir
  in
  let acl_config =
    match Sys_unix.file_exists normalized_config with
    (* | `Yes -> ()
  | `No | `Unknown -> *)
    | _ ->
      printf "Converting ClassBench format to standard format...\n";
      normalize_classbench_config classbench_config normalized_config;
      let _, acl_mat =
        List.hd_exn (read_csv_by_table normalized_config acl_schema)
      in
      let acl_mat' =
        List.map acl_mat ~f:(fun ma ->
            {
              ma with
              matches =
                Map.set ma.matches ~key:"meta.is_inbound"
                  ~data:
                    (Exact
                       (Bit.Vector.of_int ~width:2
                          (match ma.action with
                          | Name action when String.(action = "allow") ->
                            Random.int 2
                          | Name action when String.(action = "deny") -> 3
                          | _ -> failwith "unreachable")));
            })
      in
      let catch_all =
        MatchAction.make TCAM
          (Map.of_alist_exn
             (module String)
             [
               ("meta.is_inbound", Match.Ternary (Trit.Vector.wc 2));
               ("hdr.ipv4.srcAddr", Match.Ternary (Trit.Vector.wc 32));
               ("hdr.ipv4.dstAddr", Match.Ternary (Trit.Vector.wc 32));
               ("hdr.ipv4.proto", Match.Ternary (Trit.Vector.wc 8));
               ("meta.l4_sport", Match.Ternary (Trit.Vector.wc 16));
               ("meta.l4_dport", Match.Ternary (Trit.Vector.wc 16));
             ])
          (MagmaAction.make "deny")
          (Map.empty (module String))
      in
      (* printf "%s\n" (direction_mat |> Semantics.MatchActionTable.to_string); *)
      let config =
        Config.
          {
            symbols = Set.singleton (module String) "acl";
            cfg = Map.singleton (module String) "acl" (acl_mat' @ [catch_all]);
          }
      in
      config.cfg
      |> Map.fold ~init:[] ~f:(fun ~key ~data acc ->
             acc @ table_to_csv_lines ~schema:(Some acl_schema') key data)
      |> Out_channel.write_lines normalized_config;
      config
  in
  (* (src_id, tgt_id, trt_schema, translation) *)
  let all_tfxs =
    [
      ("acl", "aws", aws_schema, acl_to_aws_tfxs);
      ("acl", "azure", azure_schema, acl_to_azure_tfxs);
      ("aws", "azure", azure_schema, aws_to_azure_tfxs);
      ("azure", "aws", aws_schema, azure_to_aws_tfxs);
    ]
  in
  (* Map.iteri
    ~f:(fun ~key:op ~data:cnt -> printf "$%s$ & %d \\\\\n" op cnt)
    (List.fold all_tfxs
       ~init:(Map.empty (module String))
       ~f:(fun acc (_, _, _, _, _, tfxs) ->
         List.fold tfxs ~init:acc ~f:(fun acc (_, t) ->
             Clause.count_components acc t))); *)
  let _ =
    List.foldi all_tfxs
      ~init:(Map.singleton (module String) "acl" acl_config)
      ~f:(fun _i configs (src_id, tgt_id, output_schema, tfxs) ->
        (* printf "(%d, %d, \"%s\"),\n" (i + 1)
        (List.fold tfxs ~init:0 ~f:(fun acc (_, t) -> acc + Clause.size t))
        id; *)
        let output_file = sprintf "%s/%s_%s.csv" output_dir src_id tgt_id in
        let config = Map.find_exn configs src_id in
        printf "Input:\n%s\n"
          (config.cfg |> Map.to_alist |> List.hd_exn |> snd
         |> Fn.flip List.take 5 |> Semantics.MatchActionTable.to_string);
        let start_time = Time_ns.now () in
        let config' = transform_config tfxs config in
        let end_time = Time_ns.now () in
        printf "Output:\n%s\n"
          (config'.cfg |> Map.to_alist |> List.hd_exn |> snd
         |> Fn.flip List.take 5 |> Semantics.MatchActionTable.to_string);
        let elapsed_time_us =
          Time_ns.Span.to_ns (Time_ns.diff end_time start_time) /. 1000.0
        in
        config'.cfg
        |> Map.fold ~init:[] ~f:(fun ~key ~data acc ->
               acc @ table_to_csv_lines ~schema:(Some output_schema) key data)
        |> Out_channel.write_lines output_file;
        printf "(\"%s_%s\", %.1f),\n" src_id tgt_id elapsed_time_us;
        match Map.add configs ~key:tgt_id ~data:config' with
        | `Ok configs -> configs
        | `Duplicate -> configs)
  in
  ()
