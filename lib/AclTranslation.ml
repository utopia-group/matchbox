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
  [
    (* Step 1: project ethernet-related fields from the main ACL table *)
    {
      defined = ethernet_projected;
      definition =
        BaseLogic.Clause.MapIn
          ( acl_symbol,
            BaseLogic.MatchTfx.Project
              ["hdr.ethernet.dstAddr"; "hdr.ethernet.srcAddr"] );
    };
    (* Step 2: project ethernet-related actions *)
    {
      defined = ethernet_acl_symbol;
      definition =
        BaseLogic.Clause.MapOut
          (ethernet_projected, BaseLogic.ActionTfx.Project ["allow"; "deny"]);
    };
    (* Step 3: project IPv4-related fields *)
    {
      defined = ipv4_projected;
      definition =
        BaseLogic.Clause.MapIn
          ( acl_symbol,
            BaseLogic.MatchTfx.Project
              ["hdr.ipv4.srcAddr"; "hdr.ipv4.dstAddr"; "hdr.ipv4.proto"] );
    };
    (* Step 4: project IPv4-related actions *)
    {
      defined = ipv4_acl_symbol;
      definition =
        BaseLogic.Clause.MapOut
          (ipv4_projected, BaseLogic.ActionTfx.Project ["allow"; "deny"]);
    };
    (* Step 5: project TCP-related fields *)
    {
      defined = tcp_projected;
      definition =
        BaseLogic.Clause.MapIn
          ( acl_symbol,
            BaseLogic.MatchTfx.Project ["meta.l4_sport"; "meta.l4_dport"] );
    };
    (* Step 6: project TCP-related actions *)
    {
      defined = tcp_acl_symbol;
      definition =
        BaseLogic.Clause.MapOut
          (tcp_projected, BaseLogic.ActionTfx.Project ["allow"; "deny"]);
    };
    (* Step 7: project UDP-related fields *)
    {
      defined = udp_projected;
      definition =
        BaseLogic.Clause.MapIn
          ( acl_symbol,
            BaseLogic.MatchTfx.Project ["meta.l4_sport"; "meta.l4_dport"] );
    };
    (* Step 8: project UDP-related actions *)
    {
      defined = udp_acl_symbol;
      definition =
        BaseLogic.Clause.MapOut
          (udp_projected, BaseLogic.ActionTfx.Project ["allow"; "deny"]);
    };
    (* Step 9: project ICMP-related fields *)
    {
      defined = icmp_projected;
      definition =
        BaseLogic.Clause.MapIn
          ( acl_symbol,
            BaseLogic.MatchTfx.Project ["hdr.icmp.type"; "hdr.icmp.code"] );
    };
    (* Step 10: project ICMP-related actions *)
    {
      defined = icmp_acl_symbol;
      definition =
        BaseLogic.Clause.MapOut
          (icmp_projected, BaseLogic.ActionTfx.Project ["allow"; "deny"]);
    };
    (* Step 11: fallback ACL table (the original) *)
    {
      defined = distributed_acl_symbol;
      definition = BaseLogic.Clause.Id acl_symbol;
    };
  ]
