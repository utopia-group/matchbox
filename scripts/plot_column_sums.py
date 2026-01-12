#!/usr/bin/env python3
"""
Script to plot histograms from results.csv for different columns.
"""

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
import sys


def setup_plot_style():
    """Configure R-style plotting parameters."""
    plt.style.use('seaborn-v0_8-whitegrid')
    plt.rcParams['font.family'] = 'serif'
    plt.rcParams['font.serif'] = ["Linux Libertine", "Libertine", "Times New Roman", "Times"]
    plt.rcParams['mathtext.fontset'] = 'stix'
    plt.rcParams['text.usetex'] = True
    plt.rcParams['text.latex.preamble'] = r"\usepackage{libertine}\usepackage[libertine]{newtxmath}"
    plt.rcParams['font.size'] = 12
    plt.rcParams['axes.labelsize'] = 14
    plt.rcParams['axes.titlesize'] = 16
    plt.rcParams['xtick.labelsize'] = 12
    plt.rcParams['ytick.labelsize'] = 12


def create_histogram(data, bins, xlabel, output_filename, log_scale=False, log_base=10, symlog=False, xticks=None, integer_yticks=False):
    """Create and save a histogram with consistent styling.
    
    Args:
        data: The data to plot
        bins: Bin edges for the histogram
        xlabel: Label for x-axis
        output_filename: Output PDF filename
        log_scale: Whether to use logarithmic x-axis
        log_base: Base for logarithmic scale (default: 10, can be 2 for binary)
        symlog: Whether to use symmetric log scale (handles zero values)
        xticks: Custom x-axis tick locations (optional)
        integer_yticks: Whether to force integer tick labels on y-axis
    """
    # Create the histogram - square shape
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    counts, bin_edges, patches = ax.hist(data, bins=bins, 
                                         color='lightblue', 
                                         edgecolor='black', 
                                         linewidth=1.0,
                                         rwidth=1.0)
    
    # Set logarithmic scale if requested
    if symlog:
        ax.set_xscale('symlog', base=log_base, linthresh=0.1)
    elif log_scale:
        ax.set_xscale('log', base=log_base)
    
    # Set custom ticks if provided (but not for log scale)
    if xticks is not None and not log_scale and not symlog:
        ax.set_xticks(xticks)
    
    # Force integer ticks on y-axis if requested
    if integer_yticks:
        from matplotlib.ticker import MaxNLocator
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    
    # Add labels
    ax.set_xlabel(xlabel)
    ax.set_ylabel('Frequency')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / output_filename
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Histogram saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def plot_size(df, name):
    """Plot histogram for size column."""
    size_data = df['size']
    
    # Print statistics
    print("size Statistics:")
    print(f"  Min: {size_data.min()}")
    print(f"  Max: {size_data.max()}")
    print(f"  Mean: {size_data.mean():.2f}")
    print(f"  Median: {size_data.median()}")
    print(f"\nValue counts:")
    print(size_data.value_counts().sort_index())
    
    # Create bins
    bin_width = 5
    bins = np.arange(size_data.min() - bin_width/2, size_data.max() + bin_width, bin_width)
    
    # Set x-axis ticks at nice round numbers as integers
    min_tick = int(np.floor(size_data.min() / bin_width) * bin_width)
    max_tick = int(np.ceil((size_data.max() + 0.1) / bin_width) * bin_width)
    xticks = np.arange(min_tick, max_tick + bin_width, bin_width)
    
    # Create histogram with integer y-axis ticks
    create_histogram(size_data, bins, 'Size', f'{name}-size.pdf', xticks=xticks, integer_yticks=True)


def plot_size_ebpf(df, name):
    """Plot categorical bar chart for size column (eBPF variant)."""
    size_data = df['size']
    
    # Print statistics
    print("size Statistics:")
    print(f"  Min: {size_data.min()}")
    print(f"  Max: {size_data.max()}")
    print(f"  Mean: {size_data.mean():.2f}")
    print(f"  Median: {size_data.median()}")
    print(f"\nValue counts:")
    value_counts = size_data.value_counts().sort_index()
    print(value_counts)
    
    # Create figure
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    
    # Get unique values and counts
    unique_vals = value_counts.index.tolist()
    counts = value_counts.values.tolist()
    
    # Create categorical positions and labels
    positions = list(range(len(unique_vals)))
    labels = [str(int(val)) for val in unique_vals]
    
    # Draw bars
    bar_width = 0.6
    ax.bar(positions, counts, width=bar_width, color='lightblue', edgecolor='black', linewidth=1.0)
    
    # Set x-axis ticks and labels
    ax.set_xticks(positions)
    ax.set_xticklabels(labels)
    
    # Set x-axis limits
    ax.set_xlim(-0.5, max(positions) + 0.5)
    
    # Force integer ticks on y-axis
    from matplotlib.ticker import MaxNLocator
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    
    # Add labels
    ax.set_xlabel('Size')
    ax.set_ylabel('Frequency')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / f'{name}-size.pdf'
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Histogram saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def plot_typetime_retargeting(df):
    """Plot histogram for typetime column."""
    # Get typetime column and convert to microseconds
    typetime_ms = df['typetime']
    typetime_us = typetime_ms * 1000  # Convert to microseconds
    
    # Print statistics
    print("typetime Statistics (in microseconds):")
    print(f"  Min: {typetime_us.min():.2f} μs")
    print(f"  Max: {typetime_us.max():.2f} μs")
    print(f"  Mean: {typetime_us.mean():.2f} μs")
    print(f"  Median: {typetime_us.median():.2f} μs")
    
    # Create logarithmic bins for better distribution visualization
    bins = np.logspace(np.log10(typetime_us.min()), np.log10(typetime_us.max()), 20)
    
    # Create histogram with log scale and integer y-axis ticks
    create_histogram(typetime_us, bins, r'Typechecking Time ($\mu$s)', 'p4-time.pdf', log_scale=True, integer_yticks=True)


def plot_typetime_acl(df):
    """Plot histogram for typetime column."""
    # Get typetime column and convert to microseconds
    typetime_ms = df['typetime']
    typetime_us = typetime_ms * 1000  # Convert to microseconds
    
    # Print statistics
    print("typetime Statistics (in microseconds):")
    print(f"  Min: {typetime_us.min():.2f} μs")
    print(f"  Max: {typetime_us.max():.2f} μs")
    print(f"  Mean: {typetime_us.mean():.2f} μs")
    print(f"  Median: {typetime_us.median():.2f} μs")
    
    # Use normal linear bins instead of logarithmic
    bin_width = 5  # microseconds
    bins = np.arange(0, typetime_us.max() + bin_width, bin_width)
    
    # Set x-axis ticks at nice intervals
    min_tick = 0
    max_tick = int(np.ceil((typetime_us.max() + 0.1) / bin_width) * bin_width)
    xticks = np.arange(min_tick, max_tick + 1, bin_width)
    
    # Create histogram without log scale
    create_histogram(typetime_us, bins, r'Typechecking Time ($\mu$s)', 'cloud-time.pdf', xticks=xticks, integer_yticks=True)


def plot_typetime_ebpf(df):
    """Plot histogram for typetime column."""
    # Get typetime column and convert to microseconds
    typetime_ms = df['typetime']
    typetime_us = typetime_ms * 1000  # Convert to microseconds
    
    # Print statistics
    print("typetime Statistics (in microseconds):")
    print(f"  Min: {typetime_us.min():.2f} μs")
    print(f"  Max: {typetime_us.max():.2f} μs")
    print(f"  Mean: {typetime_us.mean():.2f} μs")
    print(f"  Median: {typetime_us.median():.2f} μs")
    
    # Create logarithmic bins for better distribution visualization
    bins = np.logspace(np.log10(typetime_us.min()), np.log10(typetime_us.max()), 20)
    
    # Create histogram with log scale and integer y-axis ticks
    create_histogram(typetime_us, bins, r'Typechecking Time ($\mu$s)', 'ebpf-time.pdf', log_scale=True, integer_yticks=True)


def plot_num_fds(df, name):
    """Plot histogram for num_fds column."""
    num_fds_data = df['num_fds']
    
    # Print statistics
    print("num_fds Statistics:")
    print(f"  Min: {num_fds_data.min()}")
    print(f"  Max: {num_fds_data.max()}")
    print(f"  Mean: {num_fds_data.mean():.2f}")
    print(f"  Median: {num_fds_data.median()}")
    print(f"\nValue counts:")
    print(num_fds_data.value_counts().sort_index())
    
    # Create bins - discrete values centered on integers
    bins = np.arange(-0.5, num_fds_data.max() + 1.5, 1)
    
    # Set x-axis ticks at the center of each bar (at integer values)
    xticks = np.arange(0, num_fds_data.max() + 1, 1)
    
    # Create histogram with integer y-axis ticks
    create_histogram(num_fds_data, bins, 'Number of Annotations', f'{name}-num-fds.pdf', xticks=xticks, integer_yticks=True)


def plot_num_fds_log(df, name):
    """Plot histogram for num_fds column with logarithmic x-axis (base 2)."""
    num_fds_data = df['num_fds']
    
    # Print statistics
    print("num_fds Statistics:")
    print(f"  Min: {num_fds_data.min()}")
    print(f"  Max: {num_fds_data.max()}")
    print(f"  Mean: {num_fds_data.mean():.2f}")
    print(f"  Median: {num_fds_data.median()}")
    print(f"\nValue counts:")
    value_counts = num_fds_data.value_counts().sort_index()
    print(value_counts)
    
    # Create custom bar chart instead of histogram
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    
    # Get unique values and their counts
    unique_vals = value_counts.index.tolist()
    counts = value_counts.values.tolist()
    
    # Separate zero and non-zero values
    zero_vals = [(v, c) for v, c in zip(unique_vals, counts) if v == 0]
    nonzero_vals = [(v, c) for v, c in zip(unique_vals, counts) if v > 0]
    
    # Use categorical positions: 0, 1, 2, ... for each unique value
    positions = []
    heights = []
    labels = []
    
    if zero_vals:
        positions.append(0)
        heights.append(zero_vals[0][1])
        labels.append('0')
    
    for i, (val, count) in enumerate(sorted(nonzero_vals), start=len(positions)):
        positions.append(i)
        heights.append(count)
        labels.append(str(int(val)))
    
    # Draw bars with uniform width
    bar_width = 0.6
    ax.bar(positions, heights, width=bar_width, color='lightblue', edgecolor='black', linewidth=1.0)
    
    # Set x-axis ticks and labels
    ax.set_xticks(positions)
    ax.set_xticklabels(labels)
    
    # Set x-axis limits to start at the edge
    ax.set_xlim(-0.5, max(positions) + 0.5)
    
    # Force integer ticks on y-axis
    from matplotlib.ticker import MaxNLocator
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    
    # Add labels
    ax.set_xlabel('Number of Annotations')
    ax.set_ylabel('Frequency')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / f'{name}-num-fds.pdf'
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Histogram saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def plot_size_fds(df, name):
    """Plot histogram for size_fds column."""
    size_fds_data = df['size_fds']
    
    # Print statistics
    print("size_fds Statistics:")
    print(f"  Min: {size_fds_data.min()}")
    print(f"  Max: {size_fds_data.max()}")
    print(f"  Mean: {size_fds_data.mean():.2f}")
    print(f"  Median: {size_fds_data.median()}")
    print(f"\nValue counts:")
    print(size_fds_data.value_counts().sort_index())
    
    # Create bins with size 5, starting from 0
    bin_width = 5
    bins = np.arange(0, size_fds_data.max() + bin_width, bin_width)
    
    # Set x-axis ticks at bin edges (ends of bars) as integers
    xticks = bins.astype(int)
    
    # Create histogram
    create_histogram(size_fds_data, bins, 'Size of Annotations', f'{name}-size-fds.pdf', xticks=xticks)


def plot_scatter_evaltime(df, name, use_jitter=False):
    """Plot scatter plot of # of rules vs eval-time, colored by target pipeline.
    
    Args:
        df: DataFrame with the data
        name: Name prefix for output file
        use_jitter: Whether to apply jitter to avoid overlap (default: False)
    """
    # Mapping of short names to full names
    name_mapping = {
        'ad': 'action_decompose',
        'ch': 'choice',
        'db': 'double',
        'ev': 'early_validate',
        'la': 'link_aggregation',
        'lo': 'logical'
    }
    
    # Extract target pipeline from name (part after underscore)
    df = df.copy()  # Avoid modifying the original dataframe
    df['target'] = df['name'].str.split('_').str[1]
    
    # Get unique targets and assign colors and markers
    targets = sorted(df['target'].unique())  # Sort for consistent colors
    colors = plt.cm.Set2(range(len(targets)))  # Use Set2 colormap for distinct colors
    color_map = dict(zip(targets, colors))
    
    # Swap colors for early_validate and logical
    if 'ev' in color_map and 'lo' in color_map:
        color_map['ev'], color_map['lo'] = color_map['lo'], color_map['ev']
    
    # Define hollow marker shapes (use fill styles)
    markers = ['o', 's', '^', 'D', 'v', 'p', '*', 'h']  # circle, square, triangle_up, diamond, triangle_down, pentagon, star, hexagon
    marker_map = dict(zip(targets, markers))
    
    # Create scatter plot
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    
    # Calculate adaptive jitter for x and y axes based on data range (only if use_jitter is True)
    if use_jitter:
        np.random.seed(42)  # For reproducibility
        x_range = df['eval_in_size'].max() - df['eval_in_size'].min()
        x_jitter_amount = max(15, x_range * 0.01)  # 1% of range or 15, whichever is larger
        
        y_range = df['eval_time'].max() - df['eval_time'].min()
        # For y-axis, use 2% of range, with a minimum to ensure visibility but avoid negatives
        # Also ensure jitter doesn't exceed half the minimum non-zero value
        y_min_nonzero = df[df['eval_time'] > 0]['eval_time'].min() if (df['eval_time'] > 0).any() else 1.0
        y_jitter_amount = max(min(y_range * 0.02, y_min_nonzero * 0.3), 0.0001)
    
    # Plot each target with its color and marker
    for target in targets:
        target_data = df[df['target'] == target]
        
        if use_jitter:
            # Add small random jitter with adaptive scaling
            x_jitter = target_data['eval_in_size'] + np.random.uniform(-x_jitter_amount, x_jitter_amount, len(target_data))
            y_jitter = target_data['eval_time'] + np.random.uniform(-y_jitter_amount, y_jitter_amount, len(target_data))
        else:
            # No jitter - use original values
            x_jitter = target_data['eval_in_size']
            y_jitter = target_data['eval_time']
        
        # Get expanded name for legend
        legend_label = name_mapping.get(target, target)
        
        ax.scatter(x_jitter, 
                  y_jitter,
                  label=legend_label,
                  marker=marker_map[target],
                  s=25,
                  facecolors='none',  # Hollow markers
                  edgecolors=color_map[target],
                  linewidth=0.8,
                  alpha=1)  # Add transparency to see overlapping markers
    
    ax.set_xlabel('Input Configuration Size')
    ax.set_ylabel('Compilation Time (ms)')
    
    ax.legend(frameon=False,
              fontsize=9, 
              handletextpad=0.3, 
              borderpad=0.5, 
              labelspacing=0.4,
              columnspacing=1.0,
              handlelength=1.5,
              loc='best')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / f"{name}-scatter-evaltime.pdf"
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Scatter plot saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def plot_scatter_evaltime_by_source(df, name, use_jitter=False):
    """Plot scatter plot of # of rules vs eval-time, colored by source pipeline.
    
    Args:
        df: DataFrame with the data
        name: Name prefix for output file
        use_jitter: Whether to apply jitter to avoid overlap (default: False)
    """
    # Mapping of short names to full names
    name_mapping = {
        'ad': 'action_decompose',
        'ch': 'choice',
        'db': 'double',
        'ev': 'early_validate',
        'la': 'link_aggregation',
        'lo': 'logical',
        'fwcpu': 'firewall (per-cpu)',
        'fwsys': 'firewall (system-wide)',
        'limitcpu': 'rate_limiter (per-cpu)',
        'limitsys': 'rate_limiter (system-wide)',
        'routecpu': 'router (per-cpu)',
        'routesys': 'router (system-wide)',
    }
    
    # Extract source pipeline from name (first element after splitting by '_')
    df = df.copy()  # Avoid modifying the original dataframe
    df['source'] = df['name'].str.split('_').str[0]
    
    # Get unique sources and assign colors and markers
    sources = sorted(df['source'].unique())  # Sort for consistent colors
    colors = plt.cm.Set2(range(len(sources)))  # Use Set2 colormap for distinct colors
    color_map = dict(zip(sources, colors))
    
    # Swap colors for early_validate and logical
    if 'ev' in color_map and 'lo' in color_map:
        color_map['ev'], color_map['lo'] = color_map['lo'], color_map['ev']
    # Swap colors for early_validate and logical
    if 'limitsys' in color_map and 'routesys' in color_map:
        color_map['limitsys'], color_map['routesys'] = color_map['routesys'], color_map['limitsys']
    
    # Define hollow marker shapes (use fill styles)
    markers = ['o', 's', '^', 'D', 'v', 'p', '*', 'h']  # circle, square, triangle_up, diamond, triangle_down, pentagon, star, hexagon
    marker_map = dict(zip(sources, markers))
    
    # Create scatter plot
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    
    # Calculate adaptive jitter for x and y axes based on data range (only if use_jitter is True)
    if use_jitter:
        np.random.seed(42)  # For reproducibility
        x_range = df['eval_in_size'].max() - df['eval_in_size'].min()
        x_jitter_amount = max(15, x_range * 0.01)  # 1% of range or 15, whichever is larger
        
        y_range = df['eval_time'].max() - df['eval_time'].min()
        # For y-axis, use 2% of range, with a minimum to ensure visibility but avoid negatives
        # Also ensure jitter doesn't exceed half the minimum non-zero value
        y_min_nonzero = df[df['eval_time'] > 0]['eval_time'].min() if (df['eval_time'] > 0).any() else 1.0
        y_jitter_amount = max(min(y_range * 0.02, y_min_nonzero * 0.3), 0.0001)
    
    # Check if max eval_time is >= 10000 ms to determine if we should convert to seconds
    max_eval_time = df['eval_time'].max()
    use_seconds = max_eval_time >= 10000
    
    # Plot each source with its color and marker
    for source in sources:
        source_data = df[df['source'] == source]
        
        if use_jitter:
            # Add small random jitter with adaptive scaling
            x_jitter = source_data['eval_in_size'] + np.random.uniform(-x_jitter_amount, x_jitter_amount, len(source_data))
            y_data = source_data['eval_time'] / 1000 if use_seconds else source_data['eval_time']
            y_jitter_divisor = 1000 if use_seconds else 1
            y_jitter = y_data + np.random.uniform(-y_jitter_amount/y_jitter_divisor, y_jitter_amount/y_jitter_divisor, len(source_data))
        else:
            # No jitter - use original values
            x_jitter = source_data['eval_in_size']
            y_jitter = source_data['eval_time'] / 1000 if use_seconds else source_data['eval_time']
       
        # Get expanded name for legend
        legend_label = name_mapping.get(source, source)
        
        ax.scatter(x_jitter, 
                  y_jitter,
                  label=legend_label,
                  marker=marker_map[source],
                  s=25,
                  facecolors='none',  # Hollow markers
                  edgecolors=color_map[source],
                  linewidth=0.8,
                  alpha=1)  # Add transparency to see overlapping markers
    
    # Set y-axis label based on whether we're using seconds or milliseconds
    ax.set_xlabel('Input Configuration Size')
    if use_seconds:
        ax.set_ylabel('Compilation Time (s)')
    else:
        ax.set_ylabel('Compilation Time (ms)')
    
    ax.legend(frameon=False,
              fontsize=9, 
              handletextpad=0.3, 
              borderpad=0.5, 
              labelspacing=0.4,
              columnspacing=1.0,
              handlelength=1.5,
              loc='best')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / f"{name}-scatter-evaltime-src.pdf"
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Scatter plot saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def plot_scatter_outsize(df, name, use_jitter=False):
    """Plot scatter plot of # of rules vs output rule count, colored by target pipeline.
    
    Args:
        df: DataFrame with the data
        name: Name prefix for output file
        use_jitter: Whether to apply jitter to avoid overlap (default: False)
    """
    # Mapping of short names to full names
    name_mapping = {
        'ad': 'action_decompose',
        'ch': 'choice',
        'db': 'double',
        'ev': 'early_validate',
        'la': 'link_aggregation',
        'lo': 'logical'
    }
    
    # Extract target pipeline from name (part after underscore)
    df = df.copy()  # Avoid modifying the original dataframe
    df['target'] = df['name'].str.split('_').str[1]
    
    # Print min and max eval_in_size
    print(f"eval_in_size Statistics:")
    print(f"  Min: {df['eval_in_size'].min()}")
    print(f"  Max: {df['eval_in_size'].max()}")
    
    # Get unique targets and assign colors and markers
    targets = sorted(df['target'].unique())  # Sort for consistent colors
    colors = plt.cm.Set2(range(len(targets)))  # Use Set2 colormap for distinct colors
    color_map = dict(zip(targets, colors))
    
    # Swap colors for early_validate and logical
    if 'ev' in color_map and 'lo' in color_map:
        color_map['ev'], color_map['lo'] = color_map['lo'], color_map['ev']
    
    # Define hollow marker shapes (use fill styles)
    markers = ['o', 's', '^', 'D', 'v', 'p', '*', 'h']  # circle, square, triangle_up, diamond, triangle_down, pentagon, star, hexagon
    marker_map = dict(zip(targets, markers))
    
    # Create scatter plot
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    
    # Calculate adaptive jitter for x and y axes based on data range (only if use_jitter is True)
    if use_jitter:
        np.random.seed(42)  # For reproducibility
        x_range = df['eval_in_size'].max() - df['eval_in_size'].min()
        x_jitter_amount = max(15, x_range * 0.01)  # 1% of range or 15, whichever is larger
        
        y_range = df['eval_out_size'].max() - df['eval_out_size'].min()
        y_jitter_amount = max(15, y_range * 0.01)  # 1% of range or 15, whichever is larger
    
    # Plot each target with its color and marker
    for target in targets:
        target_data = df[df['target'] == target]
        
        if use_jitter:
            # Add small random jitter with adaptive scaling
            x_jitter = target_data['eval_in_size'] + np.random.uniform(-x_jitter_amount, x_jitter_amount, len(target_data))
            y_jitter = target_data['eval_out_size'] + np.random.uniform(-y_jitter_amount, y_jitter_amount, len(target_data))
        else:
            # No jitter - use original values
            x_jitter = target_data['eval_in_size']
            y_jitter = target_data['eval_out_size']
        
        # Get expanded name for legend
        legend_label = name_mapping.get(target, target)
        
        ax.scatter(x_jitter, 
                  y_jitter,
                  label=legend_label,
                  marker=marker_map[target],
                  s=25,
                  facecolors='none',  # Hollow markers
                  edgecolors=color_map[target],
                  linewidth=0.8,
                  alpha=1)  # Add transparency to see overlapping markers
    
    ax.set_xlabel('Input Configuration Size')
    ax.set_ylabel('Output Configuration Size')
    
    # Format y-axis labels to show K for values >= 10000
    from matplotlib.ticker import FuncFormatter
    def format_func(value, tick_number):
        if value >= 10000:
            return f'{int(value/1000)}K'
        else:
            return f'{int(value)}'
    ax.yaxis.set_major_formatter(FuncFormatter(format_func))
    
    ax.legend(frameon=False,
              fontsize=9, 
              handletextpad=0.3, 
              borderpad=0.5, 
              labelspacing=0.4,
              columnspacing=1.0,
              handlelength=1.5,
              loc='best')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / f"{name}-scatter-outsize.pdf"
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Scatter plot saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def plot_scatter_outsize_by_source(df, name, use_jitter=False):
    """Plot scatter plot of # of rules vs output rule count, colored by source pipeline.
    
    Args:
        df: DataFrame with the data
        name: Name prefix for output file
        use_jitter: Whether to apply jitter to avoid overlap (default: False)
    """
    # Mapping of short names to full names
    name_mapping = {
        'ad': 'action_decompose',
        'ch': 'choice',
        'db': 'double',
        'ev': 'early_validate',
        'la': 'link_aggregation',
        'lo': 'logical'
    }
    
    # Extract source pipeline from name (first element after splitting by '_')
    df = df.copy()  # Avoid modifying the original dataframe
    df['source'] = df['name'].str.split('_').str[0]
    
    # Get unique sources and assign colors and markers
    sources = sorted(df['source'].unique())  # Sort for consistent colors
    colors = plt.cm.Set2(range(len(sources)))  # Use Set2 colormap for distinct colors
    color_map = dict(zip(sources, colors))
    
    # Swap colors for early_validate and logical
    if 'ev' in color_map and 'lo' in color_map:
        color_map['ev'], color_map['lo'] = color_map['lo'], color_map['ev']
    
    # Define hollow marker shapes (use fill styles)
    markers = ['o', 's', '^', 'D', 'v', 'p', '*', 'h']  # circle, square, triangle_up, diamond, triangle_down, pentagon, star, hexagon
    marker_map = dict(zip(sources, markers))
    
    # Create scatter plot
    fig, ax = plt.subplots(figsize=(3.5, 3.5))
    
    # Calculate adaptive jitter for x and y axes based on data range (only if use_jitter is True)
    if use_jitter:
        np.random.seed(42)  # For reproducibility
        x_range = df['eval_in_size'].max() - df['eval_in_size'].min()
        x_jitter_amount = max(15, x_range * 0.01)  # 1% of range or 15, whichever is larger
        
        y_range = df['eval_out_size'].max() - df['eval_out_size'].min()
        y_jitter_amount = max(15, y_range * 0.01)  # 1% of range or 15, whichever is larger
    
    # Plot each source with its color and marker
    for source in sources:
        source_data = df[df['source'] == source]
        
        if use_jitter:
            # Add small random jitter with adaptive scaling
            x_jitter = source_data['eval_in_size'] + np.random.uniform(-x_jitter_amount, x_jitter_amount, len(source_data))
            y_jitter = source_data['eval_out_size'] + np.random.uniform(-y_jitter_amount, y_jitter_amount, len(source_data))
        else:
            # No jitter - use original values
            x_jitter = source_data['eval_in_size']
            y_jitter = source_data['eval_out_size']
        
        # Get expanded name for legend
        legend_label = name_mapping.get(source, source)
        
        ax.scatter(x_jitter, 
                  y_jitter,
                  label=legend_label,
                  marker=marker_map[source],
                  s=25,
                  facecolors='none',  # Hollow markers
                  edgecolors=color_map[source],
                  linewidth=0.8,
                  alpha=1)  # Add transparency to see overlapping markers
    
    ax.set_xlabel('Input Configuration Size')
    ax.set_ylabel('Output Configuration Size')
    
    ax.legend(frameon=False,
              fontsize=9, 
              handletextpad=0.3, 
              borderpad=0.5, 
              labelspacing=0.4,
              columnspacing=1.0,
              handlelength=1.5,
              loc='best')
    
    # Remove top and right spines (R-style)
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    
    # Make remaining spines black
    ax.spines['left'].set_linewidth(0.8)
    ax.spines['bottom'].set_linewidth(0.8)
    ax.spines['left'].set_color('black')
    ax.spines['bottom'].set_color('black')
    
    # Remove grid
    ax.grid(False)
    
    # Adjust layout
    plt.tight_layout()
    
    # Save the figure as high-res PDF
    output_path = Path(__file__).parent.parent / "scripts" / f"{name}-scatter-outsize-src.pdf"
    plt.savefig(output_path, dpi=2400, bbox_inches='tight', format='pdf')
    print(f"Scatter plot saved to: {output_path}")
    
    # Close the figure to free memory
    plt.close(fig)


def compute_stats(df):
    """Compute and print statistics for size and typetime columns."""
    # Size statistics
    size_data = df['size']
    print("Size Statistics:")
    print(f"  Min: {size_data.min()}")
    print(f"  Max: {size_data.max()}")
    print(f"  Average: {size_data.mean():.2f}")
    print(f"  Median: {size_data.median()}")
    
    # Typetime statistics (convert to microseconds)
    typetime_ms = df['typetime']
    typetime_us = typetime_ms * 1000
    print("\nTypetime Statistics (in microseconds):")
    print(f"  Min: {typetime_us.min():.2f} μs")
    print(f"  Max: {typetime_us.max():.2f} μs")
    print(f"  Average: {typetime_us.mean():.2f} μs")
    print(f"  Median: {typetime_us.median():.2f} μs")
    
    # num_fds statistics
    num_fds_data = df['num_fds']
    print("\nnum_fds Statistics:")
    print(f"  Min: {num_fds_data.min()}")
    print(f"  Max: {num_fds_data.max()}")
    print(f"  Average: {num_fds_data.mean():.2f}")
    print(f"  Median: {num_fds_data.median()}")
    
    # eval_time statistics
    eval_time_data = df['eval_time']
    print("\neval_time Statistics (in milliseconds):")
    print(f"  Min: {eval_time_data.min():.2f} ms")
    print(f"  Max: {eval_time_data.max():.2f} ms")
    print(f"  Average: {eval_time_data.mean():.2f} ms")
    print(f"  Median: {eval_time_data.median():.2f} ms")


def compute_compilation_stats(df):
    """Compute and print compilation time statistics for all data together.
    
    - Average compilation time for targets of average size
    - Maximum compilation time and the size of that target
    - Average compilation time per rule
    - Max and median ratio between output and input configuration sizes
    """
    print("Compilation Time Statistics:")
    print("=" * 80)
    
    # Average compilation time and average source size (across all data)
    avg_eval_time = df['eval_time'].mean()
    avg_source_size = df['eval_in_size'].mean()
    
    # Maximum compilation time and its source size
    max_eval_time_idx = df['eval_time'].idxmax()
    max_eval_time = df.loc[max_eval_time_idx, 'eval_time']
    max_eval_time_source_size = df.loc[max_eval_time_idx, 'eval_in_size']
    
    # Average compilation time per rule
    df_copy = df.copy()
    df_copy['time_per_rule'] = df_copy['eval_time'] / df_copy['eval_in_size']
    avg_time_per_rule_ms = df_copy['time_per_rule'].mean()
    avg_time_per_rule_us = avg_time_per_rule_ms * 1000  # Convert to microseconds
    
    # Output/Input size ratio statistics
    df_copy['size_ratio'] = df_copy['eval_out_size'] / df_copy['eval_in_size']
    max_size_ratio = df_copy['size_ratio'].max()
    median_size_ratio = df_copy['size_ratio'].median()
    avg_size_ratio = df_copy['size_ratio'].mean()
    
    print(f"Average compilation time of {avg_eval_time:.2f} ms for an average of {avg_source_size:.2f} rules in source configurations")
    print(f"Maximum compilation time of {max_eval_time:.2f} ms for a source configuration with {max_eval_time_source_size} rules")
    print(f"Average compilation time per rule: {avg_time_per_rule_us:.2f} μs/rule")
    print(f"Output/Input size ratio - Max: {max_size_ratio:.2f}×, Median: {median_size_ratio:.2f}×, Average: {avg_size_ratio:.2f}×")


def main():
    csv_ret = Path(__file__).parent.parent / "programs/retargeting/results10_5K.csv"
    # csv_ret = Path(__file__).parent.parent / "programs/retargeting/results.csv"
    csv_acl = Path(__file__).parent.parent / "programs/acl/results10_alt.csv"
    # csv_acl = Path(__file__).parent.parent / "programs/acl/results_.csv"
    csv_ebpf = Path(__file__).parent.parent / "programs/ebpf/results10_alt.csv"
    # csv_ebpf = Path(__file__).parent.parent / "programs/ebpf/results.csv"
    df_ret = pd.read_csv(csv_ret)
    df_acl = pd.read_csv(csv_acl)
    df_ebpf = pd.read_csv(csv_ebpf)
    
    # Check for --jitter flag
    use_jitter = '--jitter' in sys.argv
    if use_jitter:
        sys.argv.remove('--jitter')
    
    # Determine which plot to create based on command line argument
    if len(sys.argv) > 1:
        plot_type = sys.argv[1].lower()
    else:
        # No argument provided - run all plots
        plot_type = 'all'
    
    # Handle stats mode separately (doesn't need plot style)
    if plot_type == 'prog_stats_ret':
        compute_stats(df_ret)
        return
    if plot_type == 'prog_stats_acl':
        compute_stats(df_acl)
        return
    if plot_type == 'prog_stats_ebpf':
        compute_stats(df_ebpf)
        return
    
    # Handle compilation stats mode
    if plot_type == 'comp_stats_ret':
        compute_compilation_stats(df_ret)
        return
    if plot_type == 'comp_stats_acl':
        compute_compilation_stats(df_acl)
        return
    if plot_type == 'comp_stats_ebpf':
        compute_compilation_stats(df_ebpf)
        return
    
    # Setup plotting style for all other modes
    setup_plot_style()
    
    # Run all plots if no specific mode was given
    if plot_type == 'all':
        plot_size(df_ret, 'p4')
        plot_size(df_acl, 'acl')
        plot_typetime_retargeting(df_ret)
        plot_typetime_acl(df_acl)
        plot_num_fds(df_ret, 'p4')
        plot_num_fds(df_acl, 'acl')
        plot_size_fds(df_acl, 'acl')
        plot_scatter_evaltime(df_ret, 'p4', use_jitter)
        plot_scatter_evaltime(df_acl, 'acl', use_jitter)
        plot_scatter_outsize(df_ret, 'p4', use_jitter)
        plot_scatter_outsize(df_acl, 'acl', use_jitter)
        print("All plots completed!")
        return

    if plot_type == 'size_ret':
        plot_size(df_ret, 'p4')
    if plot_type == 'size_acl':
        plot_size(df_acl, 'acl')
    if plot_type == 'size_ebpf':
        plot_size_ebpf(df_ebpf, 'ebpf')
    elif plot_type == 'typetime_ret':
        plot_typetime_retargeting(df_ret)
    elif plot_type == 'typetime_acl':
        plot_typetime_acl(df_acl)
    elif plot_type == 'typetime_ebpf':
        plot_typetime_ebpf(df_ebpf)
    elif plot_type == 'num_fds_ret':
        plot_num_fds(df_ret, 'p4')
    elif plot_type == 'num_fds_acl':
        plot_num_fds(df_acl, 'acl')
    elif plot_type == 'num_fds_ebpf':
        plot_num_fds_log(df_ebpf, 'ebpf')
    elif plot_type == 'size_fds_acl':
        plot_size_fds(df_acl, 'acl')
    elif plot_type == 'scatter_time_ret':
        plot_scatter_evaltime(df_ret, 'p4', use_jitter)
    elif plot_type == 'scatter_time_acl':
        plot_scatter_evaltime(df_acl, 'cloud', use_jitter)
    elif plot_type == 'scatter_time_ebpf':
        plot_scatter_evaltime(df_ebpf, 'ebpf', use_jitter)
    elif plot_type == 'scatter_time_src_ret':
        plot_scatter_evaltime_by_source(df_ret, 'p4', use_jitter)
    elif plot_type == 'scatter_time_src_acl':
        plot_scatter_evaltime_by_source(df_acl, 'cloud', use_jitter)
    elif plot_type == 'scatter_time_src_ebpf':
        plot_scatter_evaltime_by_source(df_ebpf, 'ebpf', use_jitter)
    elif plot_type == 'scatter_outsize_ret':
        plot_scatter_outsize(df_ret, 'p4', use_jitter)
    elif plot_type == 'scatter_outsize_acl':
        plot_scatter_outsize(df_acl, 'cloud', use_jitter)
    elif plot_type == 'scatter_outsize_ebpf':
        plot_scatter_outsize(df_ebpf, 'ebpf', use_jitter)
    elif plot_type == 'scatter_outsize_src_ret':
        plot_scatter_outsize_by_source(df_ret, 'p4', use_jitter)
    elif plot_type == 'scatter_outsize_src_acl':
        plot_scatter_outsize_by_source(df_acl, 'cloud', use_jitter)
    else:
        print(f"Unknown plot type: {plot_type}")
        print("Available options: size_ret, size_acl, typetime_ret, typetime_acl, num_fds_ret, num_fds_acl, size_fds_acl, scatter_time_ret, scatter_time_acl, scatter_time_src_ret, scatter_time_src_acl, scatter_outsize_ret, scatter_outsize_acl, scatter_outsize_src_ret, scatter_outsize_src_acl, stats, comp_stats_ret, comp_stats_acl, or no argument to run all")
        print("Add --jitter flag to enable jitter on scatter plots")
        sys.exit(1)


if __name__ == "__main__":
    main()
