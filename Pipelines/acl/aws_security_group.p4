
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

action allow () { meta.allow = true; };
action deny () { meta.allow = false; }

table inbound_acl {
    key = {
      hdr.ipv4.srcAddr : lpm;
      hdr.ipv4.proto : exact;
      meta.l4_sport : ternary;
    }
    actions = {
        allow; 
        deny
    }
    default_action = allow()
    max_rules = 40;
}


table outbound_acl {
    key = {
      hdr.ipv4.dstAddr : lpm;
      hdr.ipv4.proto : exact;
      meta.l4_dport : ternary;
    }
    actions = {
        allow; 
        deny
    }
    default_action = allow()
    max_rules = 40;
}

apply {
    direction.apply();
    if (meta.unknown){ exit; }
    if (meta.is_inbound){ 
        inbound_acl.apply();
    } else {
        outbound_acl.apply();
    }
}
  

