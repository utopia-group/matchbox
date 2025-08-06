
#include <core.p4>
#include <v1model.p4>  
// HEADERS

// Define header types

header eth_type_t {
  bit<16> value;
}
header ethernet_t {
  bit<48> srcAddr;
  bit<48> dstAddr;
}
header ipv4_t {
  bit<8> ttl;
  bit<32> srcAddr;
  bit<8> protocol;
  bit<32> dstAddr;
  bit<6> dscp;
}
header tcp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
header udp_t {
  bit<16> srcPort;
  bit<16> dstPort;
}
// Assemble headers in a single struct
struct my_headers_t {
  eth_type_t eth_type;
  ethernet_t ethernet;
  icmp_t icmp;
  inner_icmp_t inner_icmp;
  inner_ipv4_t inner_ipv4;
  ipv4_t ipv4;
  tcp_t tcp;
  udp_t udp;
}

  
// METADATA
struct my_metadata_t {
  bit<16> l4_sport;
  bit<16> l4_dport;
}
// PARSER

parser MyParser(
  packet_in packet,
  out my_headers_t hdr,
  inout my_metadata_t meta,
  inout standard_metadata_t standard_metadata)
{
  // Parser state machine   
  state parse_eth_type {
    packet.extract(hdr.eth_type);
    transition select(hdr.eth_type.value){
      (16w34887) : parse_mpls;
      (16w2048) : parse_ipv4;
      default : accept;
    }

  }

  state parse_ethernet {
    packet.extract(hdr.ethernet);
    transition parse_eth_type
  }
  
  state parse_icmp {
    packet.extract(hdr.icmp);
    transition accept;
  }    

  state parse_ipv4 {
    packet.extract(hdr.ipv4);
    transition select(hdr.ipv4.protocol){
      (8w6) : parse_tcp;
      (8w17) : parse_udp;
      (8w1) : parse_icmp;
      default : accept;
    }

  }

  state parse_tcp {
    packet.extract(hdr.tcp);
    meta.l4_sport = hdr.tcp.srcPort;
    meta.l4_dport = hdr.tcp.dstPort;
    transition accept;
  }
    

  state parse_udp {
    packet.extract(hdr.udp);
    meta.l4_sport = hdr.udp.srcPort;
    meta.l4_dport = hdr.udp.dstPort;
    transition accept;
  }
    
  state start {
    transition parse_ethernet;
  }    
}

// INGRESS

control MyIngress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
  action allow () { };
  action deny () { standard_metadata.egress_port = 9w511; }

  table ethernet_acl {
    key = {
      hdr.ethernet.dstAddr : ternary;
      hdr.ethernet.srcAddr : ternary;
    }
    actions = {
      allow;
      deny;
    }
  }

  table ipv4_acl {
    key = {
      hdr.ipv4.srcAddr : ternary;
      hdr.ipv4.dstAddr : ternary;
      hdr.ipv4.proto : ternary;
    }
    actions = {
      allow;
      deny
    }
  }
  table tcp_acl {
    key = {
      hdr.tcp.sport : ternary;
      hdr.tcp.dport : ternary;
    }
    actions = {
      allow;
      deny
    }
  }

  table udp_acl {
    key = {
      hdr.udp.sport : ternary;
      hdr.upd.dport : ternary;
    }
    actions = {
      allow;
      deny;
    }
  }

  table icmp_acl {
    key = {
      hdr.icmp.code : ternary;
      hdr.icmp.type : ternary;
    }
    allow;
    deny;
  }


  table acl {
    key = {
      hdr.ethernet.dstAddr : ternary;
      hdr.ethernet.srcAddr : ternary;
      hdr.vlan_tag.vlan_id : ternary;
      hdr.eth_type.value : ternary;
      hdr.ipv4.srcAddr : ternary;
      hdr.ipv4.srcAddr : ternary;
      hdr.ipv4.proto : ternary;
      hdr.icmp.type : ternary;
      hdr.icmp.code : ternary;
      meta.l4_sport : ternary;
      meta.l4_dport : ternary;
    }
    actions = {
        allow; 
        deny
    }
  }
  apply {
    ethernet_acl.apply();
    if (ipv4.isValid()){
      ipv4_acl.apply();
    }
    if (tcp.isValid()){
      tcp_acl.apply();
    }
    if (udp.isValid()){
      udp_acl.apply();
    }
    if (icmp.isValid()){
      icmp.apply()
    }
    acl.apply();
  }
}
  
// EGRESS

control MyEgress (
  inout my_headers_t hdr,
  inout my_metadata_t meta, 
  inout standard_metadata_t standard_metadata)
{
    apply {}
}
  
// OTHER
control MyVerifyChecksum(
    inout my_headers_t   hdr,
    inout my_metadata_t  meta)
{
    apply {     }
}

control MyComputeChecksum(
    inout my_headers_t  hdr,
    inout my_metadata_t meta)
{
    apply {   }
}
control MyDeparser(
    packet_out      packet,
    in my_headers_t hdr)
{
    apply {
    }
}
V1Switch(
    MyParser(),
    MyVerifyChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;
  
