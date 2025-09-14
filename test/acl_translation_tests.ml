open Core
open Stijl
open Alcotest

(* Initial type context for translating classbench_acl.p4 to distributed_acl.p4 *)
let create_acl_type_context () : Type.ctx =
  let open Type in
  Map.of_alist_exn
    (module String)
    [
      ( "acl",
        Table
          {
            keys =
              Map.of_alist_exn
                (module String)
                [
                  ("hdr.ethernet.dstAddr", (48, Ternary));
                  ("hdr.ethernet.srcAddr", (48, Ternary));
                  ("hdr.vlan_tag.vlan_id", (16, Ternary));
                  ("hdr.eth_type.value", (16, Ternary));
                  ("hdr.ipv4.srcAddr", (32, Ternary));
                  ("hdr.ipv4.dstAddr", (32, Ternary));
                  ("hdr.ipv4.proto", (8, Ternary));
                  ("hdr.icmp.type", (8, Ternary));
                  ("hdr.icmp.code", (8, Ternary));
                  ("meta.l4_sport", (16, Ternary));
                  ("meta.l4_dport", (16, Ternary));
                ];
            actions = String.Set.of_list ["allow"; "deny"];
            data = Map.of_alist_exn (module String) [];
          } );
    ]

let test_acl_translation_typechecks () =
  let translation = AclTranslation.acl_translation in
  let type_ctx = create_acl_type_context () in
  (* Verify that each step in the translation typechecks *)
  let final_ctx, all_typecheck =
    List.fold translation ~init:(type_ctx, true) ~f:(fun (ctx, success) step ->
        try
          let inferred_table =
            BaseLogic.Clause.typeof_exn (BaseChecker.infer ctx step.definition)
          in
          let new_ctx =
            Map.set ctx ~key:step.defined.name ~data:(Type.Table inferred_table)
          in
          (new_ctx, success)
        with _ ->
          (* Type error occurred *)
          (ctx, false))
  in
  check bool "All translation steps typecheck" true all_typecheck;
  (* Verify that we can access the final defined symbols *)
  let expected_symbols =
    [
      "ethernet_projected";
      "ethernet_acl";
      "ipv4_projected";
      "ipv4_acl";
      "tcp_projected";
      "tcp_acl";
      "udp_projected";
      "udp_acl";
      "icmp_projected";
      "icmp_acl";
      "distributed_acl";
    ]
  in
  List.iter expected_symbols ~f:(fun symbol_name ->
      check bool
        (sprintf "Symbol '%s' is defined in final type context" symbol_name)
        true
        (Map.mem final_ctx symbol_name))

(* Test that symbols reference the correct P4 table names *)
let test_acl_translation_symbols () =
  (* Check that the main symbols have the expected names *)
  check string "ACL symbol name" "acl" AclTranslation.acl.name;
  check string "Ethernet ACL symbol name" "ethernet_acl"
    AclTranslation.ethernet_acl.name;
  check string "IPv4 ACL symbol name" "ipv4_acl" AclTranslation.ipv4_acl.name;
  check string "TCP ACL symbol name" "tcp_acl" AclTranslation.tcp_acl.name;
  check string "UDP ACL symbol name" "udp_acl" AclTranslation.udp_acl.name;
  check string "ICMP ACL symbol name" "icmp_acl" AclTranslation.icmp_acl.name;
  check string "Distributed ACL symbol name" "distributed_acl"
    AclTranslation.distributed_acl.name
