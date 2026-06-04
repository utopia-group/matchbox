#!/usr/bin/env python3
"""Runnable version of the Figure 4 intro example.

This script follows the control-flow shape of the pseudocode in Figure 4:
it inspects Route_S, walks ACL_S in priority order, and constructs ACL_T.
To make the example executable on the Figure 2 configuration, it also applies
the two fixes called out in the overview footnote:

1. use reachability rather than a raw prefix-existence check, and
2. add intersecting routed prefixes in the overlap case.

CIDR manipulation is implemented with the ``ipaddr`` library as requested.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


VENDOR_DIR = Path(__file__).resolve().parent / "vendor"
if str(VENDOR_DIR) not in sys.path:
    sys.path.insert(0, str(VENDOR_DIR))

try:
    import ipaddr
except ImportError as exc:  # pragma: no cover - helpful failure for manual use.
    raise SystemExit(
        "Could not import the vendored 'ipaddr' package. "
        "Install it into code/intro_example/vendor first."
    ) from exc


IPv4Network = ipaddr.IPv4Network


@dataclass(frozen=True)
class Rule:
    cidr: IPv4Network
    action: str
    data: tuple[tuple[str, int], ...] = field(default_factory=tuple)

    def with_action(self, action: str) -> "Rule":
        return Rule(self.cidr, action, self.data)


def make_rule(cidr: str, action: str, **data: int) -> Rule:
    return Rule(IPv4Network(cidr), action, tuple(sorted(data.items())))


def format_rule(rule: Rule) -> str:
    cidr = str(rule.cidr)
    if rule.data:
        payload = ", ".join(f"{key}={value}" for key, value in rule.data)
        return f"{cidr:18} -> {rule.action}({payload})"
    return f"{cidr:18} -> {rule.action}"


def unique_networks(networks: Iterable[IPv4Network]) -> list[IPv4Network]:
    seen: set[IPv4Network] = set()
    ordered: list[IPv4Network] = []
    for network in networks:
        if network not in seen:
            seen.add(network)
            ordered.append(network)
    return ordered


def unique_rules(rules: Iterable[Rule]) -> list[Rule]:
    seen: set[Rule] = set()
    ordered: list[Rule] = []
    for rule in rules:
        if rule not in seen:
            seen.add(rule)
            ordered.append(rule)
    return ordered


def intersect(lhs: IPv4Network, rhs: IPv4Network) -> IPv4Network | None:
    if lhs in rhs:
        return lhs
    if rhs in lhs:
        return rhs
    return None


def subtract_networks(
    networks: Iterable[IPv4Network], cut: IPv4Network
) -> list[IPv4Network]:
    remaining: list[IPv4Network] = []
    for network in networks:
        if cut in network:
            remaining.extend(network.address_exclude(cut))
        elif network in cut:
            continue
        else:
            remaining.append(network)
    return remaining


def effective_miss_regions(route_s: Iterable[Rule]) -> list[IPv4Network]:
    remaining = [IPv4Network("0.0.0.0/0")]
    for rule in route_s:
        if rule.action == "miss":
            continue
        # remaining = subtract_networks(remaining, rule.cidr)
        remaining.append (rule.cidr)
    return unique_networks(remaining)


def reachable_subnets(
    cidr: IPv4Network, miss_regions: Iterable[IPv4Network]
) -> list[IPv4Network]:
    remaining = [cidr]
    for miss_region in miss_regions:
        remaining = subtract_networks(remaining, miss_region)
    return unique_networks(remaining)


def intersecting_routed_prefixes(cidr: IPv4Network, route_s: Iterable[Rule]) -> list[IPv4Network]:
    overlaps: list[IPv4Network] = []
    for rule in route_s:
        if rule.action == "miss":
            continue
        shared = intersect(cidr, rule.cidr)
        if shared is not None:
            overlaps.append(shared)
    return unique_networks(overlaps)


def compute_acl_T(route_s: list[Rule], acl_s: list[Rule]) -> list[Rule]:
    """Compute ACL_T from Figure 4, made executable for Figure 2's CIDRs."""

    acl_t: list[Rule] = []
    denies = effective_miss_regions(route_s)

    for rule in acl_s:
        if rule.action != "allow":
            print(f"adding non-allow rule {format_rule(rule)}")
            acl_t.append(rule)
        if rule.cidr in denies:
            print(f"denying {format_rule(rule)}")
            acl_t.append(rule.with_action("deny"))
        else:
            print(f"copying {format_rule(rule)}")
            acl_t.append(rule)

    return unique_rules(acl_t)


def figure_2_source_configuration() -> tuple[list[Rule], list[Rule]]:
    route_s = [
        make_rule("10.1.9.0/24", "route", port=9),
        make_rule("10.1.1.0/24", "route", port=1),
        make_rule("10.1.0.0/16", "route", port=2),
        make_rule("0.0.0.0/0", "miss"),
    ]
    acl_s = [
        make_rule("10.1.0.10/32", "deny"),
        make_rule("10.1.10.0/24", "deny"),
        make_rule("10.0.0.0/8", "allow"),
        make_rule("0.0.0.0/0", "allow")
    ]
    return route_s, acl_s


def main() -> int:
    route_s, acl_s = figure_2_source_configuration()
    acl_t = compute_acl_T(route_s, acl_s)

    print("Route_S (Figure 2)")
    for rule in route_s:
        print(f"  {format_rule(rule)}")

    print("\nACL_S (Figure 2)")
    for rule in acl_s:
        print(f"  {format_rule(rule)}")

    print("\nComputed ACL_T")
    for rule in acl_t:
        print(f"  {format_rule(rule)}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
