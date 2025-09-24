

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


action allow () { meta.allow = true; }
action deny () { meta.allow = false; }

table acl {
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
    default_action = allow()
    max_rules = 1000;
}

apply {
    direction.apply();
    if (meta.unknown){ exit; }
    acl.apply();
    if (!meta.allow) {
        standard_metadata(mark_to_drop);
    }
}
  

