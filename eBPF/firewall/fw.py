"""
Program to generate the tables for routing configurations.
Can generate port forwarding rules with two types of states: "per_cpu" and "system_wide".
"""

import sys
import json
import random
import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate forwarding configuration tables.")
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
                        parts = line.split('\t')
                        ip = parts[0][1:]  # The first IP starts with a '@'
                        ports = parts[2].split(':')
                        ports = (int(ports[0].strip()), int(ports[1].strip()))
                        rule_list[ip.strip()] = ports
        except Exception as e:
            print(f"Error reading IP file: {e}")
            sys.exit(1)

    all_configs = []
    for _ in range(num_configs):
        # Generation variables -- at each generation, the following variables introduce randomness.
        num_cpus = random.choice([2, 4, 8, 10, 12, 16, 20, 24, 32])

        config = []
        for rule in rule_list.items():
            rule_config = {}
            rule_config["table"] = "port_forward"

            ip_mask, ports = rule
            if state_type == "per_cpu":
                rule_config["matches"] = {
                    "ip_mask": ip_mask
                }
            else:
                rule_config["matches"] = {
                    "ip_mask": ip_mask,
                    "cpu_id": random.randint(0, num_cpus - 1)
                }
            rule_config["action"] = ["forward"]
            rule_config["data"] = {
                "port_low": ports[0],
                "port_high": ports[1],
            }
            config.append(rule_config)

        all_configs.append(config)

    with open(output_file, "w") as f:
        json.dump(all_configs, f, indent=2)