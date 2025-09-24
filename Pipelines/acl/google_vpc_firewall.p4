
action allow () { meta.allow = true; };
action deny () { meta.allow = false; }

action seen () {
    meta.seen = true;
}


action inbound () {
    meta.is_inbound = true;
}
action outbound () {
    meta.is_inbound = false;
}
action unknown () {
    meta.unknown = true;
}

private table direction {
    key = {
        meta.ingress_port : exact;
    } 
    actions = { inbound; outbound; unknown}
    default_action = unknown();
}

private table ipv4_state {
    key = {
        meta.is_inbound : exact;
        meta.ip_srcAddr : exact;
        meta.ip_dstAddr : exact;
        hdr.ipv4.proto : exact;
        meta.l4_sport : ternary;
        meta.l4_dport : ternary
    }
    action = {seen; not_seen}
    default_action = not_seen()
}

public table acl {
    key = {
      meta.is_inbound : exact;
      hdr.ipv4.proto : exact;
      hdr.ipv4.srcAddr : lpm;
      hdr.ipv4.dstAddr : lpm;
      meta.l4_sport : ternary;
      meta.l4_dport : ternary;
    }
    actions = {
        allow; 
        deny
    }
    default_action = allow();

}

apply { // assume meta is zero-initialized
    direction.apply();
    if (!meta.unknown && hdr.ethernet.type = 0x800 && hdr.ipv4.proto in {TCP, UDP, ICMP, SCTP}) { // IPV4
        l4 = hdr.tcp ? hdr.ipv4.proto = TCP : 
             hdr.udp ? hdr.ipv4.proto = UDP :
             hdr.icmp ? hdr.ipv4.proto = ICMP :
             hdr.sctp;
        meta.l4_dport = hdr.tcp.dPort;
        meta.l4_sport = hdr.tcp.sPort;
        acl.apply();
        if (meta.allow){
            ipv4_state.add({!meta.is_inbound, 
                            hdr.ipv4.srcAddr, 
                            hdr.ipv4.dstAddr, 
                            hdr.ipv4.proto, 
                            l4.sPort,
                            l4.dPort}, 10s);
        } else {
            // swap header
            meta.is_inbound = true;
            meta.ip_dstAddr = hdr.ipv4.srcAddr;
            meta.ip_srcAddr = hdr.ipv4.dstAddr;
            meta.l4_sport = l4.dPort;
            meta.l4_dport = l4.sPort;
            ipv4_state.apply()
            bool seen = meta.seen;
            meta.is_inbound = false;
            seen = seen || meta.seen;
            if (seen) {
                meta.allow = true;
            }
        }
    }
    if (!meta.allow){
        mark_to_drop(standard_metadata);
    }
}
