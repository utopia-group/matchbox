open Core
open Gpl

(* classbench_acl.p4 table symbol *)
let acl = BaseLogic.Symbol.make "acl" [] 0

(* distributed_acl.p4 table symbols *)
let ethernet_acl = BaseLogic.Symbol.make "ethernet_acl" [] 0
let ipv4_acl = BaseLogic.Symbol.make "ipv4_acl" [] 0
let tcp_acl = BaseLogic.Symbol.make "tcp_acl" [] 0
let udp_acl = BaseLogic.Symbol.make "udp_acl" [] 0
let icmp_acl = BaseLogic.Symbol.make "icmp_acl" [] 0
let distributed_acl = BaseLogic.Symbol.make "distributed_acl" [] 0

let acl_translation : BaseLogic.t list =
  let ethDst = Var.make "hdr.ethernet.dstAddr" 48 in
  let ethSrc = Var.make "hdr.ethernet.srcAddr" 48 in
  let ipSrc = Var.make "hdr.ipv4.srcAddr" 32 in
  let ipDst = Var.make "hdr.ipv4.dstAddr" 32 in
  let ipProto = Var.make "hdr.ipv4.proto" 8 in
  let l4DstPort = Var.make "meta.l4_dport" 16 in
  let l4SrcPort = Var.make "meta.l4_sport" 16 in
  let icmpType = Var.make "hdr.icmp.type" 8 in
  let icmpCode = Var.make "hdr.icmp.code" 8 in

  let open BaseLogic in
  let open Clause in
  [
    {defined = ethernet_acl; definition = Project [ethSrc; ethDst] <<| id acl};
    {
      defined = ipv4_acl;
      definition = Project [ipSrc; ipDst; ipProto] <<| id acl;
    };
    {
      defined = tcp_acl;
      definition =
        (let tcp_proto_filter =
           Map.singleton
             (module String)
             "hdr.ipv4.proto"
             (Semantics.Match.Exact (Bit.Vector.of_int ~width:8 6))
         in
         Project [l4SrcPort; l4DstPort]
         <<| (MatchTfx.CubeFilter tcp_proto_filter <<| id acl));
    };
    {
      defined = udp_acl;
      definition =
        (let udp_proto_filter =
           Map.singleton
             (module String)
             "hdr.ipv4.proto"
             (Semantics.Match.Exact (Bit.Vector.of_int ~width:8 17))
         in
         Project [l4SrcPort; l4DstPort]
         <<| (MatchTfx.CubeFilter udp_proto_filter <<| id acl));
    };
    {
      defined = icmp_acl;
      definition =
        (let icmp_proto_filter =
           Map.singleton
             (module String)
             "hdr.ipv4.proto"
             (Semantics.Match.Exact (Bit.Vector.of_int ~width:8 1))
         in
         Project [icmpType; icmpCode]
         <<| (MatchTfx.CubeFilter icmp_proto_filter <<| id acl));
    };
    (* {defined = distributed_acl; definition = id acl}; *)
  ]
