"""
Program to generate the tables for rate limiter configurations.
"""

import sys
import json
import random
import argparse

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate rate limiter configuration tables.")
    parser.add_argument(
        "--limit_type",
        type=str,
        choices=["per_cpu", "system_wide"],
        default="system_wide",
        help="Type of rate limiter config to generate (default: system_wide)",
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
    limit_type = args.limit_type
    num_configs = args.num_configs
    output_file = args.output_file
    if not output_file:
        output_file = f"limit_{limit_type}.json"

    all_configs = []
    for _ in range(num_configs):
        # Generation variables -- at each generation, the following variables introduce randomness.
        num_cpus = random.choice([2, 4, 8, 10, 12, 16, 20, 24, 32])

        config = {}
        if limit_type == "per_cpu":
            per_cpu_limit = random.randint(50, 200)
            config["table"] = "rate_limit"
            config["matches"] = {}
            config["action"] = ["limit"]
            config["data"] = {
                "num_cpus": num_cpus,
                "per_cpu_limit": per_cpu_limit,
            }
        elif limit_type == "system_wide":
            system_wide_limit = num_cpus * random.randint(50, 200)
            config["table"] = "rate_limit"
            config["matches"] = {}
            config["action"] = ["limit"]
            config["data"] = {
                "num_cpus": num_cpus,
                "system_wide_limit": system_wide_limit,
            }

        all_configs.append([config])

    with open(output_file, "w") as f:
        json.dump(all_configs, f, indent=2)