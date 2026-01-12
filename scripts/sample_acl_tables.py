#!/usr/bin/env python3
"""
Sample subsets of acl and ipv4_state tables from acl.json.
Creates n files with evenly-spaced table sizes from minimal to full size,
maintaining corresponding indices between acl and ipv4_state tables.
"""

import json
import sys
import os
from pathlib import Path


def load_json(filepath):
    """Load the JSON data from the file."""
    with open(filepath, 'r') as f:
        return json.load(f)


def is_wildcard_rule(entry):
    """
    Check if an entry is a catch-all rule with wildcard keys.
    Wildcards can be:
    - All asterisks (e.g., "***", "********", "****************")
    - All 0s with /0 prefix for LPM fields (e.g., "00000000000000000000000000000000/0")
    """
    matches = entry.get('matches', {})
    if not matches:
        return False
    
    for value in matches.values():
        value_str = str(value)
        
        # Check if it's an all-asterisk wildcard
        if '*' in value_str and all(c in ['*', '/'] for c in value_str):
            continue
        
        # Check if it's an all-0s with /0 LPM wildcard
        if '/' in value_str:
            parts = value_str.split('/')
            if len(parts) == 2 and parts[1] == '0' and all(c == '0' for c in parts[0]):
                continue
        
        # If we get here, this value is not a wildcard
        return False
    
    return True


def separate_tables(data):
    """Separate entries by table type and identify catch-all rules."""
    acl_entries = []
    ipv4_state_entries = []
    acl_catchall = None
    ipv4_state_catchall = None
    other_entries = []
    
    for entry in data:
        table_name = entry.get('table', '')
        if table_name == 'acl':
            if is_wildcard_rule(entry):
                acl_catchall = entry
            else:
                acl_entries.append(entry)
        elif table_name == 'ipv4_state':
            if is_wildcard_rule(entry):
                ipv4_state_catchall = entry
            else:
                ipv4_state_entries.append(entry)
        else:
            other_entries.append(entry)
    
    return acl_entries, ipv4_state_entries, acl_catchall, ipv4_state_catchall, other_entries


def create_sample(acl_entries, ipv4_state_entries, acl_catchall, ipv4_state_catchall, 
                  other_entries, sample_size):
    """
    Create a sample with the specified number of acl/ipv4_state entries.
    Maintains the same indices in both tables.
    Always includes the catch-all rules at the end.
    """
    sampled_acl = acl_entries[:sample_size]
    sampled_ipv4_state = ipv4_state_entries[:sample_size]
    
    # Add catch-all rules if they exist
    if acl_catchall:
        sampled_acl.append(acl_catchall)
    if ipv4_state_catchall:
        sampled_ipv4_state.append(ipv4_state_catchall)
    
    # Combine: other entries + sampled acl + sampled ipv4_state
    return other_entries + sampled_acl + sampled_ipv4_state


def generate_experiments_json(template_file, sample_sizes, base_name, output_dir):
    """
    Generate experiments.json file with duplicated experiments for each sample size.
    
    Args:
        template_file: Path to the template experiments.json file
        sample_sizes: List of sample sizes that were generated
        base_name: Base name of the sampled files (e.g., "acl")
        output_dir: Directory where sample files were saved (as string or Path)
    """
    # Load template experiments
    template_experiments = load_json(template_file)
    
    # Convert output_dir to string for path manipulation, preserving the original path
    if output_dir is None:
        raise ValueError("output_dir cannot be None")
    
    if isinstance(output_dir, Path):
        output_dir_str = str(output_dir)
    else:
        output_dir_str = output_dir
    
    # Normalize the path separators to forward slashes for consistency
    output_dir_str = output_dir_str.replace('\\', '/')
    
    # Generate new experiments for each sample
    new_experiments = []
    
    for size in sample_sizes:
        for exp in template_experiments:
            # Create a copy of the experiment
            new_exp = exp.copy()
            
            # Update the name to include the sample size
            original_name = exp['name']
            new_exp['name'] = f"{original_name}_{size}"
            
            # Update the input path to use output_dir
            input_path = exp['input']
            input_filename = input_path.split('/')[-1]  # Extract just the filename
            
            # Replace the base filename with the sampled version
            if f"{base_name}.json" == input_filename:
                new_input_filename = f"{base_name}{size}.json"
            elif input_filename.startswith(base_name + "_"):
                # e.g., acl_ad.json -> acl1_ad.json
                suffix = input_filename[len(base_name):-5]  # e.g., "_ad"
                new_input_filename = f"{base_name}{size}{suffix}.json"
            else:
                # Keep original filename
                new_input_filename = input_filename
            
            new_exp['input'] = f"{output_dir_str}/{new_input_filename}"
            
            # Update the output path to use output_dir
            output_path = exp['output']
            output_filename = output_path.split('/')[-1]  # Extract just the filename
            
            # Handle different naming patterns in output files
            # Pattern 1: acl_ad.json -> acl1_ad.json
            if output_filename.startswith(base_name + "_"):
                suffix = output_filename[len(base_name):-5]  # e.g., "_ad"
                new_output_filename = f"{base_name}{size}{suffix}.json"
            # Pattern 2: ad_acl.json -> ad_acl1.json
            elif f"_{base_name}.json" in output_filename:
                prefix = output_filename[:-(len(base_name) + 5)]  # e.g., "ad_"
                new_output_filename = f"{prefix}{base_name}{size}.json"
            # Pattern 3: ad_ch.json -> ad1_ch.json
            else:
                # Find pattern like "xx_yy.json" and insert size after first part
                name_parts = output_filename[:-5].split('_', 1)  # Split on first underscore
                if len(name_parts) == 2:
                    new_output_filename = f"{name_parts[0]}{size}_{name_parts[1]}.json"
                else:
                    new_output_filename = output_filename
            
            new_exp['output'] = f"{output_dir_str}/{new_output_filename}"
            
            new_experiments.append(new_exp)
    
    # Save the new experiments.json file in the parent directory of output_dir
    # For path like ../programs/acl/data/experiment5, we want ../programs/acl
    output_dir_path = Path(output_dir_str)
    # Go up two levels: experiment5 -> data -> acl
    experiments_output_dir = output_dir_path.parent.parent
    output_file = experiments_output_dir / f"experiments{len(sample_sizes)}.json"
    with open(output_file, 'w') as f:
        json.dump(new_experiments, f, indent=4)
    
    print(f"\nGenerated experiments file: {output_file}")
    print(f"  Total experiments: {len(new_experiments)}")
    print(f"  Original template experiments: {len(template_experiments)}")
    print(f"  Samples: {len(sample_sizes)}")
    
    return output_file


def generate_samples(input_file, num_samples, output_dir=None, experiments_template=None):
    """
    Generate num_samples evenly-spaced subsets of the tables.
    
    Args:
        input_file: Path to the input JSON file
        num_samples: Number of sample files to create
        output_dir: Directory to save output files (default: same as input)
        experiments_template: Path to experiments.json template file (optional)
    """
    # Load data
    data = load_json(input_file)
    acl_entries, ipv4_state_entries, acl_catchall, ipv4_state_catchall, other_entries = separate_tables(data)
    
    # Verify both tables have the same size
    if len(acl_entries) != len(ipv4_state_entries):
        print(f"Warning: acl table has {len(acl_entries)} entries, "
              f"ipv4_state table has {len(ipv4_state_entries)} entries")
    
    max_size = min(len(acl_entries), len(ipv4_state_entries))
    print(f"Total acl entries: {len(acl_entries)}")
    print(f"Total ipv4_state entries: {len(ipv4_state_entries)}")
    if acl_catchall:
        print(f"ACL catch-all rule found: {acl_catchall.get('matches', {})}")
    if ipv4_state_catchall:
        print(f"IPv4_state catch-all rule found: {ipv4_state_catchall.get('matches', {})}")
    print(f"Other entries: {len(other_entries)}")
    print(f"Max sample size: {max_size}")
    
    # Preserve the original output_dir string for experiments.json paths
    output_dir_str = output_dir
    
    # Determine output directory
    if output_dir is None:
        output_dir = Path(input_file).parent
    else:
        output_dir = Path(output_dir)
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Calculate sample sizes evenly distributed from 1 to max_size
    # We avoid size 0 as requested
    if num_samples == 1:
        sample_sizes = [max_size]
    else:
        # Evenly space from minimal (1) to maximum
        step = (max_size - 1) / (num_samples - 1)
        sample_sizes = [int(1 + i * step) for i in range(num_samples)]
        # Ensure the last one is exactly max_size
        sample_sizes[-1] = max_size
    
    # Generate sample files
    base_name = Path(input_file).stem  # Get filename without extension
    
    for i, size in enumerate(sample_sizes):
        sample_data = create_sample(acl_entries, ipv4_state_entries, 
                                   acl_catchall, ipv4_state_catchall,
                                   other_entries, size)
        
        output_file = output_dir / f"{base_name}{size}.json"
        
        with open(output_file, 'w') as f:
            json.dump(sample_data, f, indent=2)
        
        print(f"Created sample {i+1}/{num_samples}: {output_file}")
        print(f"  Table size: {size} entries each (acl & ipv4_state) + catch-all rules")
        print(f"  Total entries: {len(sample_data)}")
    
    # Generate experiments.json if template is provided
    if experiments_template and os.path.exists(experiments_template):
        generate_experiments_json(experiments_template, sample_sizes, base_name, output_dir_str)
    
    return sample_sizes


def main():
    if len(sys.argv) < 3:
        print("Usage: python sample_acl_tables.py <input_file> <num_samples> [output_dir] [experiments_template]")
        print("Example: python sample_acl_tables.py programs/acl/data/acl.json 5")
        print("Example: python sample_acl_tables.py programs/acl/data/acl.json 5 output_samples/")
        print("Example: python sample_acl_tables.py programs/acl/data/acl.json 5 programs/acl/data/experiment5 programs/acl/experiments.json")
        sys.exit(1)
    
    input_file = sys.argv[1]
    num_samples = int(sys.argv[2])
    output_dir = sys.argv[3] if len(sys.argv) > 3 else None
    experiments_template = sys.argv[4] if len(sys.argv) > 4 else None
    
    if not os.path.exists(input_file):
        print(f"Error: Input file '{input_file}' not found")
        sys.exit(1)
    
    if num_samples < 1:
        print("Error: Number of samples must be at least 1")
        sys.exit(1)
    
    if experiments_template and not os.path.exists(experiments_template):
        print(f"Warning: Experiments template file '{experiments_template}' not found")
        experiments_template = None
    
    generate_samples(input_file, num_samples, output_dir, experiments_template)
    print("\nDone!")


if __name__ == "__main__":
    main()
