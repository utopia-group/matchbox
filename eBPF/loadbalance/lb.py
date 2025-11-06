"""
Program to generate the tables for load balancer configurations.
"""

import sys
import json
import random
import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate load balancer configuration tables.")
    parser.add_argument(
        "--lb_type",
        type=str,
        choices=["consistent", "plain"],
        default="consistent",
        help="Type of load balancer to generate (default: consistent)",
    )
    parser.add_argument(
        "--num_configs",
        type=int,
        default=100,
        help="Number of configurations to generate (default: 100)",
    )
    parser.add_argument(
        "--output_file",
        type=str,
        help="Output file to write the configuration (default: lb_<lb_type>.json)",
    )
    args = parser.parse_args()
    lb_type = args.lb_type
    num_configs = args.num_configs
    output_file = args.output_file
    if not output_file:
        output_file = f"lb_{lb_type}.json"

    all_configs = []
    for _ in range(num_configs):
        # Generation variables -- at each generation, the following variables introduce randomness.
        num_cpus = random.choice([2, 4, 8, 10, 12, 16, 20, 24, 32])
        bucket_factor = random.randint(8, 32)

        config = {}
        if lb_type == "consistent":
            config["table"] = "consistent_lb"
            config["matches"] = {}
            config["action"] = ["load_balance"]
            config["data"] = {
                "num_cpus": num_cpus,
                "bucket_map": [i % num_cpus for i in range(bucket_factor * num_cpus)],
                "system_wide_limit": num_cpus * 100,
            }
        elif lb_type == "plain":
            config["table"] = "plain_lb"
            config["matches"] = {}
            config["action"] = ["load_balance"]
            config["data"] = {
                "num_cpus": num_cpus,
                "per_cpu_limit": 100,
            }

        all_configs.append([config])

    with open(output_file, "w") as f:
        json.dump(all_configs, f, indent=2)