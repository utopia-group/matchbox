open Gpl

(* classbench_acl.p4 table symbol *)
let acl_symbol = BaseLogic.Symbol.make "acl" [] 0

(* distributed_acl.p4 table symbols *)
let ethernet_acl_symbol = BaseLogic.Symbol.make "ethernet_acl" [] 0
let ipv4_acl_symbol = BaseLogic.Symbol.make "ipv4_acl" [] 0
let tcp_acl_symbol = BaseLogic.Symbol.make "tcp_acl" [] 0
let udp_acl_symbol = BaseLogic.Symbol.make "udp_acl" [] 0
let icmp_acl_symbol = BaseLogic.Symbol.make "icmp_acl" [] 0
let distributed_acl_symbol = BaseLogic.Symbol.make "distributed_acl" [] 0

(* Intermediate table symbols *)
let ethernet_projected = BaseLogic.Symbol.make "ethernet_projected" [] 0
let ipv4_projected = BaseLogic.Symbol.make "ipv4_projected" [] 0
let tcp_projected = BaseLogic.Symbol.make "tcp_projected" [] 0
let udp_projected = BaseLogic.Symbol.make "udp_projected" [] 0
let icmp_projected = BaseLogic.Symbol.make "icmp_projected" [] 0

let acl_translation : BaseLogic.t list =
  let ethDst = Var.make "hdr.ethernet.dstAddr" 48 in
  let ethSrc = Var.make "hdr.ethernet.dstAddr" 48 in 
  let ipSrc = Var.make "hdr.ipv4.srcAddr" 32 in 
  let ipDst = Var.make "hdr.ipv4.dstAddr" 32 in 
  let ipProto = Var.make "hdr.ipv4.proto" 16 in
  let l4DstPort = Var.make "meta.l4_dport" 16 in 
  let l4SrcPort = Var.make "meta.l4_sport" 16 in 
  let icmpType = Var.make "hdr.icmp.type" 8 in 
  let icmpCode = Var.make "hdr.icmp.code" 8 in 

  let open BaseLogic in 
  let open Clause in 
  [
    (* Step 1: project ethernet-related fields from the main ACL table *)
    {
      defined = ethernet_projected;
      definition =
          Project [ethSrc; ethDst] <<| id acl_symbol
    };
    (* Step 2: project ethernet-related actions *)
    {
      defined = ethernet_acl_symbol;
      definition = failwith "@Robert! attention!"
        (* @robert --- not sure what you mean to do here.. cannot project actions? *)
        (* MapOut (Id ethernet_projected, Project ["allow"; "deny"], None); *)
    };
    (* Step 3: project IPv4-related fields *)
    {
      defined = ipv4_projected;
      definition = 
        Project [ipSrc; ipDst; ipProto] <<| id acl_symbol
    };
    (* Step 4: project IPv4-related actions *)
    {
      defined = ipv4_acl_symbol;
      definition =failwith "@Robert! attention!"
        (* @robert --- not sure what you mean to do here.. cannot project actions? *)
(*         MapOut
          (Id ipv4_projected, Project ["allow"; "deny"], None); *)
    };
    (* Step 5: project TCP-related fields *)
    {
      defined = tcp_projected;
      definition = (*@ Robert I think this needs a filter w.r.t the ipProto value for TCP *)
        Project [l4SrcPort; l4DstPort] <<| id acl_symbol
    };
    (* Step 6: project TCP-related actions *)
    {
      defined = tcp_acl_symbol;
      definition = failwith "@Robert! attention!"
        (* @robert --- not sure what you mean to do here.. cannot project actions? *)
        (* MapOut
          (Id tcp_projected, Project ["allow"; "deny"], None); *)
    };
    (* Step 7: project UDP-related fields *)
    {
      defined = udp_projected;
      definition = (*@ Robert I think this needs a filter w.r.t the ipProto value for UDP *)
        Project [l4SrcPort; l4DstPort] <<| id acl_symbol
    };
    (* Step 8: project UDP-related actions *)
    {
      defined = udp_acl_symbol;
      definition =failwith "@Robert! attention!"
        (* @robert --- not sure what you mean to do here.. cannot project actions? *)
        (* MapOut
          (Id udp_projected, Project ["allow"; "deny"], None); *)
    };
    (* Step 9: project ICMP-related fields *)
    {
      defined = icmp_projected;
      definition = (*@ Robert I think this needs a filter w.r.t the ipProto value for ICMP *)
        Project [icmpType; icmpCode] <<| id acl_symbol
    };
    (* Step 10: project ICMP-related actions *)
    {
      defined = icmp_acl_symbol;
      definition = failwith "@Robert! attention!"
        (* @robert --- not sure what you mean to do here.. cannot project actions? *)
        (* MapOut
          (Id icmp_projected, Project ["allow"; "deny"], None); *)
    };
    (* Step 11: fallback ACL table (the original) *)
    (* {
      defined = distributed_acl_symbol;
      definition = BaseLogic.Clause.Id acl_symbol;
    }; *)
  ]
