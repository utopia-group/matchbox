#!/usr/bin/env python3
"""
Sample subsets of eBPF configuration files from programs/ebpf/data.
Creates n files with evenly-spaced sizes from minimal to full size.

For *cpu.json files: Balances rules across 32 acl tables (acl0-acl31)
For *sys.json files: Balances rules across 32 cpu_id values (00000-11111 in binary)
"""

import json
import sys
import os
from pathlib import Path
from collections import defaultdict


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
    
    for key, value in matches.items():
        value_str = str(value)
        
        # Skip cpu_id field for sys files - it's not a wildcard indicator
        if key == 'cpu_id':
            continue
        
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


def separate_by_table(data):
    """
    Separate entries by table name (for *cpu.json files).
    Returns dict mapping table name to (regular_entries, wildcard_entry) tuple.
    """
    tables = defaultdict(lambda: ([], None))
    for entry in data:
        table_name = entry.get('table', '')
        regular_entries, wildcard = tables[table_name]
        if is_wildcard_rule(entry):
            tables[table_name] = (regular_entries, entry)
        else:
            regular_entries.append(entry)
            tables[table_name] = (regular_entries, wildcard)
    return dict(tables)


def separate_by_cpu_id(data):
    """
    Separate entries by cpu_id (for *sys.json files).
    Returns dict mapping cpu_id to (regular_entries, wildcard_entry) tuple.
    """
    cpu_groups = defaultdict(lambda: ([], None))
    for entry in data:
        cpu_id = entry.get('matches', {}).get('cpu_id', '')
        regular_entries, wildcard = cpu_groups[cpu_id]
        if is_wildcard_rule(entry):
            cpu_groups[cpu_id] = (regular_entries, entry)
        else:
            regular_entries.append(entry)
            cpu_groups[cpu_id] = (regular_entries, wildcard)
    return dict(cpu_groups)


def create_balanced_sample_cpu(tables_dict, sample_size):
    """
    Create a balanced sample for *cpu.json files.
    Takes sample_size entries from each table (acl0-acl31).
    Always includes wildcard rules at the end.
    
    Args:
        tables_dict: Dict mapping table name to (regular_entries, wildcard_entry) tuple
        sample_size: Number of regular entries to take from each table
    
    Returns:
        List of sampled entries
    """
    sampled = []
    for table_name in sorted(tables_dict.keys()):
        regular_entries, wildcard = tables_dict[table_name]
        # Take first sample_size regular entries from this table
        sampled.extend(regular_entries[:sample_size])
        # Always add wildcard rule if it exists
        if wildcard:
            sampled.append(wildcard)
    return sampled


def create_balanced_sample_sys(cpu_groups_dict, sample_size):
    """
    Create a balanced sample for *sys.json files.
    Takes sample_size entries from each cpu_id group.
    Always includes wildcard rules at the end.
    
    Args:
        cpu_groups_dict: Dict mapping cpu_id to (regular_entries, wildcard_entry) tuple
        sample_size: Number of regular entries to take from each cpu_id
    
    Returns:
        List of sampled entries
    """
    sampled = []
    for cpu_id in sorted(cpu_groups_dict.keys()):
        regular_entries, wildcard = cpu_groups_dict[cpu_id]
        # Take first sample_size regular entries from this cpu_id
        sampled.extend(regular_entries[:sample_size])
        # Always add wildcard rule if it exists
        if wildcard:
            sampled.append(wildcard)
    return sampled


def generate_experiments_json(template_file, sample_sizes, output_dir):
    """
    Generate experiments.json file with duplicated experiments for each sample size.
    
    Args:
        template_file: Path to the template experiments.json file
        sample_sizes: List of sample sizes that were generated
        output_dir: Directory where sample files were saved
    """
    # Load template experiments
    template_experiments = load_json(template_file)
    
    # Convert output_dir to string for path manipulation
    if isinstance(output_dir, Path):
        output_dir_str = str(output_dir)
    else:
        output_dir_str = output_dir
    
    # Normalize the path separators
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
            
            # Update the input path
            input_path = exp['input']
            # Extract just the filename from the path
            input_filename = input_path.split('/')[-1]
            base_name = input_filename.rsplit('.', 1)[0]  # Remove .json extension
            
            # Create new filename with sample size
            new_input_filename = f"{base_name}{size}.json"
            new_exp['input'] = f"{output_dir_str}/{new_input_filename}"
            
            new_experiments.append(new_exp)
    
    # Save the new experiments.json file in the parent directory of output_dir
    output_dir_path = Path(output_dir_str)
    experiments_output_dir = output_dir_path.parent.parent
    output_file = experiments_output_dir / f"experiments{len(sample_sizes)}.json"
    
    with open(output_file, 'w') as f:
        json.dump(new_experiments, f, indent=4)
    
    print(f"\nGenerated experiments file: {output_file}")
    print(f"  Total experiments: {len(new_experiments)}")
    print(f"  Original template experiments: {len(template_experiments)}")
    print(f"  Samples per experiment: {len(sample_sizes)}")
    
    return output_file


def generate_samples_for_file(input_file, num_samples, output_dir):
    """
    Generate num_samples evenly-spaced subsets for a single file.
    
    Args:
        input_file: Path to the input JSON file
        num_samples: Number of sample files to create
        output_dir: Directory to save output files
    
    Returns:
        List of sample sizes generated
    """
    # Load data
    data = load_json(input_file)
    filename = Path(input_file).name
    base_name = filename.rsplit('.', 1)[0]
    
    # Determine file type and organize data
    if base_name.endswith('cpu'):
        # File like fwcpu.json, limitcpu.json, routecpu.json
        tables_dict = separate_by_table(data)
        num_groups = len(tables_dict)
        # Get regular entries and wildcard from first table
        first_table = next(iter(tables_dict.values()))
        regular_entries, wildcard = first_table
        entries_per_group = len(regular_entries)
        has_wildcards = wildcard is not None
        group_type = "table"
        
        print(f"\nProcessing {filename} (per-CPU mode):")
        print(f"  Total entries: {len(data)}")
        print(f"  Number of tables: {num_groups}")
        print(f"  Regular entries per table: {entries_per_group}")
        if has_wildcards:
            print(f"  Wildcard rules: Found (will be preserved in all samples)")
        
    elif base_name.endswith('sys'):
        # File like fwsys.json, limitsys.json, routesys.json
        cpu_groups_dict = separate_by_cpu_id(data)
        num_groups = len(cpu_groups_dict)
        # Get regular entries and wildcard from first cpu_id
        first_group = next(iter(cpu_groups_dict.values()))
        regular_entries, wildcard = first_group
        entries_per_group = len(regular_entries)
        has_wildcards = wildcard is not None
        group_type = "cpu_id"
        
        print(f"\nProcessing {filename} (system-wide mode):")
        print(f"  Total entries: {len(data)}")
        print(f"  Number of CPU IDs: {num_groups}")
        print(f"  Regular entries per CPU ID: {entries_per_group}")
        if has_wildcards:
            print(f"  Wildcard rules: Found (will be preserved in all samples)")
    else:
        raise ValueError(f"Unknown file type: {filename}")
    
    # Calculate sample sizes evenly distributed
    if num_samples == 1:
        sample_sizes = [entries_per_group]
    else:
        # Evenly space from 1 to entries_per_group
        step = (entries_per_group - 1) / (num_samples - 1)
        sample_sizes = [int(1 + i * step) for i in range(num_samples)]
        # Ensure the last one is exactly the maximum
        sample_sizes[-1] = entries_per_group
    
    # Generate sample files
    for i, size in enumerate(sample_sizes):
        if group_type == "table":
            sample_data = create_balanced_sample_cpu(tables_dict, size)
        else:  # cpu_id
            sample_data = create_balanced_sample_sys(cpu_groups_dict, size)
        
        output_file = output_dir / f"{base_name}{size}.json"
        
        with open(output_file, 'w') as f:
            json.dump(sample_data, f, indent=2)
        
        print(f"  Created sample {i+1}/{num_samples}: {output_file.name}")
        print(f"    Size per {group_type}: {size} entries")
        print(f"    Total entries: {len(sample_data)} ({num_groups} × {size})")
    
    return sample_sizes


def generate_all_samples(data_dir, num_samples, output_dir=None, experiments_template=None):
    """
    Generate samples for all 6 eBPF configuration files.
    
    Args:
        data_dir: Directory containing the original data files
        num_samples: Number of sample levels to create
        output_dir: Directory to save output files (default: same as data_dir)
        experiments_template: Path to experiments.json template file (optional)
    """
    data_dir = Path(data_dir)
    
    # Determine output directory
    if output_dir is None:
        output_dir = data_dir
    else:
        output_dir = Path(output_dir)
    
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # List of all 6 configuration files
    config_files = [
        'fwcpu.json',
        'fwsys.json',
        'limitcpu.json',
        'limitsys.json',
        'routecpu.json',
        'routesys.json'
    ]
    
    # Generate samples for each file
    all_sample_sizes = []
    for config_file in config_files:
        input_file = data_dir / config_file
        if not input_file.exists():
            print(f"Warning: {config_file} not found in {data_dir}")
            continue
        
        sample_sizes = generate_samples_for_file(input_file, num_samples, output_dir)
        all_sample_sizes.append(sample_sizes)
    
    # Generate experiments.json if template is provided
    if experiments_template and os.path.exists(experiments_template):
        # Use the sample sizes from the first file (they should all be the same structure)
        generate_experiments_json(experiments_template, all_sample_sizes[0], output_dir)
    
    print("\nDone!")
    print(f"Generated {num_samples} sample levels for {len(config_files)} configuration files")
    print(f"Output directory: {output_dir}")


def main():
    if len(sys.argv) < 3:
        print("Usage: python sample_ebpf_data.py <data_dir> <num_samples> [output_dir] [experiments_template]")
        print("Example: python sample_ebpf_data.py programs/ebpf/data 5")
        print("Example: python sample_ebpf_data.py programs/ebpf/data 5 programs/ebpf/data")
        print("Example: python sample_ebpf_data.py programs/ebpf/data 5 programs/ebpf/data programs/ebpf/experiments.json")
        sys.exit(1)
    
    data_dir = sys.argv[1]
    num_samples = int(sys.argv[2])
    output_dir = sys.argv[3] if len(sys.argv) > 3 else None
    experiments_template = sys.argv[4] if len(sys.argv) > 4 else None
    
    if not os.path.exists(data_dir):
        print(f"Error: Data directory '{data_dir}' not found")
        sys.exit(1)
    
    if num_samples < 1:
        print("Error: Number of samples must be at least 1")
        sys.exit(1)
    
    if experiments_template and not os.path.exists(experiments_template):
        print(f"Warning: Experiments template file '{experiments_template}' not found")
        experiments_template = None
    
    generate_all_samples(data_dir, num_samples, output_dir, experiments_template)


if __name__ == "__main__":
    main()
