"""
Program to generate the tables for routing configurations.
Can generate port forwarding rules with two types of states: "per_cpu" and "system_wide".
"""

import sys
import json
import random
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
        help="Output file to write the configuration (default: route_<state_type>.json)",
    )
    args = parser.parse_args()
    state_type = args.state_type
    num_configs = args.num_configs
    rules_file = args.rules_file

    output_file = args.output_file
    if not output_file:
        output_file = f"route_{state_type}.json"

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
                        src_port_range = parts[2].split(":")
                        dst_port_range = parts[3].split(":")

                        # Use just one port from the ranges.
                        src_port = random.randint(
                            int(src_port_range[0].strip()),
                            int(src_port_range[1].strip()),
                        )
                        dst_port = random.randint(
                            int(dst_port_range[0].strip()),
                            int(dst_port_range[1].strip()),
                        )
                        rule_list[ip.strip()] = (src_port, dst_port)
        except Exception as e:
            print(f"Error reading IP file: {e}")
            sys.exit(1)

    # Process rule_list to convert IP addresses and ports to binary format
    processed_rules = []
    for ip_mask, (src_port, dst_port) in rule_list.items():
        binary_ip_mask = parse_ip_cidr(ip_mask)
        binary_src_port = format(src_port, "016b")
        binary_dst_port = format(dst_port, "016b")
        processed_rules.append((binary_ip_mask, (binary_src_port, binary_dst_port)))
    rule_list = processed_rules

    num_cpus = 32

    config = []
    if state_type == "per_cpu":
        # Per CPU mode: create separate tables for each CPU
        for cpu_id in range(num_cpus):
            for rule in rule_list:
                rule_config = {}
                rule_config["table"] = f"port_forward{cpu_id}"
                ip_mask, port = rule
                rule_config["matches"] = {"ip_mask": ip_mask}
                rule_config["action"] = ["forward"]
                rule_config["data"] = {
                    "src_port": port[0],
                    "dst_port": port[1],
                }
                rule_config["priority"] = 100
                config.append(rule_config)
            config.append(
                {
                    "table": f"port_forward{cpu_id}",
                    "matches": {"ip_mask": "00000000000000000000000000000000/0"},
                    "action": ["nop"],
                    "data": {},
                    "priority": 101,
                }
            )
    else:
        # System-wide mode: single table with cpu_id as a match field
        for cpu_id in range(num_cpus):
            for rule in rule_list:
                rule_config = {}
                rule_config["table"] = "port_forward"

                ip_mask, port = rule
                rule_config["matches"] = {
                    "ip_mask": ip_mask,
                    "cpu_id": format(cpu_id, "05b"),
                }
                rule_config["action"] = ["forward"]
                rule_config["data"] = {
                    "src_port": port[0],
                    "dst_port": port[1],
                }
                rule_config["priority"] = 100
                config.append(rule_config)
        config.append(
            {
                "table": "port_forward",
                "matches": {
                    "ip_mask": "00000000000000000000000000000000/0",
                    "cpu_id": "*****",
                },
                "action": ["nop"],
                "data": {},
                "priority": 101,
            }
        )

    with open(output_file, "w") as f:
        json.dump(config, f, indent=2)
