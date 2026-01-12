#!/usr/bin/env python3
"""
Convert ClassBench CSV format to ACL JSON format.
Maps CSV fields to JSON format with appropriate wildcards and binary encoding.
"""

import json
import re
import random
import sys
from pathlib import Path


def parse_ip_cidr(ip_cidr):
    """
    Parse IP address with CIDR notation and convert to binary format.
    
    Args:
        ip_cidr: String like "192.168.1.0/24"
    
    Returns:
        Binary string with /prefix notation like "11000000101010000000000100000000/24"
    """
    if '/' not in ip_cidr:
        ip_cidr = f"{ip_cidr}/32"
    
    ip_part, prefix = ip_cidr.split('/')
    octets = ip_part.split('.')
    
    # Convert each octet to 8-bit binary
    binary_parts = []
    for octet in octets:
        binary_parts.append(format(int(octet), '08b'))
    
    binary_ip = ''.join(binary_parts)
    return f"{binary_ip}/{prefix}"


def port_to_binary(port):
    """
    Convert port number to 16-bit binary string.
    
    Args:
        port: Integer port number
    
    Returns:
        16-bit binary string
    """
    return format(int(port), '016b')


def proto_to_binary(proto):
    """
    Convert protocol number to 8-bit binary string.
    
    Args:
        proto: Integer protocol number
    
    Returns:
        8-bit binary string
    """
    return format(int(proto), '08b')


def parse_classbench_rule(rule_line):
    """
    Parse a single ClassBench CSV rule line.
    
    Args:
        rule_line: String containing comma-separated field=value pairs
    
    Returns:
        Dictionary with parsed fields
    """
    fields = {}
    
    # Split by comma and parse each field
    parts = [p.strip() for p in rule_line.split(',')]
    
    for part in parts:
        if '=' not in part:
            continue
        
        key, value = part.split('=', 1)
        key = key.strip()
        value = value.strip()
        
        fields[key] = value
    
    return fields


def convert_to_acl_json(csv_file, output_file):
    """
    Convert ClassBench CSV to ACL JSON format.
    Generates both acl and ipv4_state tables.
    ipv4_state has the same rules as acl but with is_inbound bit flipped.
    
    Args:
        csv_file: Path to input CSV file
        output_file: Path to output JSON file
    """
    all_rules = []
    
    with open(csv_file, 'r') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            
            # Parse the ClassBench rule
            fields = parse_classbench_rule(line)
            
            # Build the base matches (shared between acl and ipv4_state)
            base_matches = {}
            
            # Map nw_src to srcAddr (LPM field)
            if 'nw_src' in fields:
                base_matches['srcAddr'] = parse_ip_cidr(fields['nw_src'])
            else:
                # Wildcard: all 0s with /0 prefix
                base_matches['srcAddr'] = '00000000000000000000000000000000/0'
            
            # Map nw_dst to dstAddr (LPM field)
            if 'nw_dst' in fields:
                base_matches['dstAddr'] = parse_ip_cidr(fields['nw_dst'])
            else:
                # Wildcard: all 0s with /0 prefix
                base_matches['dstAddr'] = '00000000000000000000000000000000/0'
            
            # Map tp_src to l4_sport (16-bit exact match)
            if 'tp_src' in fields:
                base_matches['l4_sport'] = port_to_binary(fields['tp_src'])
            else:
                # Wildcard: all *
                base_matches['l4_sport'] = '****************'
            
            # Map tp_dst to l4_dport (16-bit exact match)
            if 'tp_dst' in fields:
                base_matches['l4_dport'] = port_to_binary(fields['tp_dst'])
            else:
                # Wildcard: all *
                base_matches['l4_dport'] = '****************'
            
            # Map nw_proto to proto (8-bit exact match)
            if 'nw_proto' in fields:
                base_matches['proto'] = proto_to_binary(fields['nw_proto'])
            else:
                # Wildcard: all *
                base_matches['proto'] = '********'
            
            # Generate random is_inbound bit for acl table
            is_inbound_acl = str(random.randint(0, 1))
            
            # Create ACL rule entry
            acl_matches = base_matches.copy()
            acl_matches['is_inbound'] = is_inbound_acl
            
            acl_rule = {
                "table": "acl",
                "matches": acl_matches,
                "action": ["allow"],  # Default action
                "data": {},
                "priority": 100
            }
            
            all_rules.append(acl_rule)
            
            # Create ipv4_state rule entry with flipped is_inbound bit
            ipv4_state_matches = base_matches.copy()
            ipv4_state_matches['is_inbound'] = '1' if is_inbound_acl == '0' else '0'
            
            ipv4_state_rule = {
                "table": "ipv4_state",
                "matches": ipv4_state_matches,
                "action": ["seen"],  # ipv4_state uses "seen" action
                "data": {},
                "priority": 100
            }
            
            all_rules.append(ipv4_state_rule)
    
    # Write to JSON file
    with open(output_file, 'w') as f:
        json.dump(all_rules, f, indent=2)
    
    num_rules_per_table = len(all_rules) // 2
    print(f"Converted {num_rules_per_table} rules from {csv_file}")
    print(f"Generated {num_rules_per_table} acl rules and {num_rules_per_table} ipv4_state rules")
    print(f"Total {len(all_rules)} rules written to {output_file}")
    return len(all_rules)


def main():
    if len(sys.argv) < 2:
        print("Usage: python classbench_to_acl_json.py <input_csv> [output_json]")
        print("Example: python classbench_to_acl_json.py programs/acl/_classbench_acl_inserts_5000.csv")
        print("Example: python classbench_to_acl_json.py programs/acl/_classbench_acl_inserts_5000.csv programs/acl/data/classbench_acl.json")
        sys.exit(1)
    
    input_file = sys.argv[1]
    
    # Determine output file
    if len(sys.argv) > 2:
        output_file = sys.argv[2]
    else:
        # Default: same directory as input, with .json extension
        input_path = Path(input_file)
        output_file = input_path.parent / f"{input_path.stem}.json"
    
    if not Path(input_file).exists():
        print(f"Error: Input file '{input_file}' not found")
        sys.exit(1)
    
    # Set random seed for reproducibility
    random.seed(42)
    
    convert_to_acl_json(input_file, output_file)
    print("Done!")


if __name__ == "__main__":
    main()
