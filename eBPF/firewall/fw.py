"""
Program to generate the tables for routing configurations.
Can generate port forwarding rules with two types of states: "per_cpu" and "system_wide".
"""

import sys
import json
import argparse


def parse_ip_cidr(ip_cidr):
    """
    Parse IP address with CIDR notation and convert to binary format.

    Args:
        ip_cidr: String like "192.168.1.0/24"

    Returns:
        Binary string with /prefix notation like "11000000101010000000000100000000/24"
    """
    if "/" not in ip_cidr:
        ip_cidr = f"{ip_cidr}/32"

    ip_part, prefix = ip_cidr.split("/")
    octets = ip_part.split(".")

    # Convert each octet to 8-bit binary
    binary_parts = []
    for octet in octets:
        binary_parts.append(format(int(octet), "08b"))

    binary_ip = "".join(binary_parts)
    return f"{binary_ip}/{prefix}"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate forwarding configuration tables."
    )
    parser.add_argument(
        "--state_type",
        type=str,
        choices=["per_cpu", "system_wide"],
        default="system_wide",
        help="Type of routing state to generate (default: system_wide)",
    )
    parser.add_argument(
        "--num_configs",
        type=int,
        default=100,
        help="Number of configurations to generate (default: 100)",
    )
    parser.add_argument(
        "--rules_file",
        type=str,
        help="File containing list of IPs/IP masks to generate rules for",
    )
    parser.add_argument(
        "--output_file",
        type=str,
        help="Output file to write the configuration (default: firewall_<state_type>.json)",
    )
    args = parser.parse_args()
    state_type = args.state_type
    num_configs = args.num_configs
    rules_file = args.rules_file

    output_file = args.output_file
    if not output_file:
        output_file = f"firewall_{state_type}.json"

    # If ip_file is not provided use a default set of IPs
    if not rules_file:
        rule_list = {
            "10.10.1.1/32": (1000, 1000),
            "10.1.1.1/24": (5000, 5000),
        }
    else:
        # Load IPs from file
        try:
            rule_list = {}
            with open(rules_file, "r") as f:
                for line in f:
                    line = line.strip()
                    if line:
                        parts = line.split("\t")
                        ip = parts[0][1:]  # The first IP starts with a '@'
                        ports = parts[2].split(":")
                        ports = (int(ports[0].strip()), int(ports[1].strip()))
                        rule_list[ip.strip()] = ports
        except Exception as e:
            print(f"Error reading IP file: {e}")
            sys.exit(1)

    # Process rule_list to convert IP addresses to binary format
    processed_rules = []
    for ip_mask, (port_low, port_high) in rule_list.items():
        binary_ip_mask = parse_ip_cidr(ip_mask)
        binary_port_low = format(port_low, "016b")
        binary_port_high = format(port_high, "016b")
        processed_rules.append((binary_ip_mask, (binary_port_low, binary_port_high)))
    rule_list = processed_rules

    num_cpus = 32

    config = []

    if state_type == "per_cpu":
        # Per CPU mode: create separate tables for each CPU
        for cpu_id in range(num_cpus):
            for rule in rule_list:
                rule_config = {}
                rule_config["table"] = f"acl{cpu_id}"
                ip_mask, _ = rule
                rule_config["matches"] = {"ip_mask": ip_mask}
                rule_config["action"] = ["allow"]
                rule_config["data"] = {}
                rule_config["priority"] = 100
                config.append(rule_config)
            config.append(
                {
                    "table": f"acl{cpu_id}",
                    "matches": {"ip_mask": "00000000000000000000000000000000/0"},
                    "action": ["deny"],
                    "data": {},
                    "priority": 101,
                }
            )
    else:
        # System-wide mode: single table with cpu_id as a match field
        for cpu_id in range(num_cpus):
            for rule in rule_list:
                rule_config = {}
                rule_config["table"] = "acl"
                ip_mask, port = rule
                rule_config["matches"] = {
                    "ip_mask": ip_mask,
                    "cpu_id": format(cpu_id, "05b"),
                }
                rule_config["action"] = ["allow"]
                rule_config["data"] = {}
                rule_config["priority"] = 100
                config.append(rule_config)
        config.append(
            {
                "table": "acl",
                "matches": {
                    "ip_mask": "00000000000000000000000000000000/0",
                    "cpu_id": "*****",
                },
                "action": ["deny"],
                "data": {},
                "priority": 101,
            }
        )

    with open(output_file, "w") as f:
        json.dump(config, f, indent=2)
