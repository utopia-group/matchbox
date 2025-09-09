#!/usr/bin/env python3

import sys
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

def create_plot(df, x_col, y_col, title, ylabel, color, output_file):
    plt.figure(figsize=(10, 6))
    plt.plot(df[x_col], df[y_col], f'{color}o-', linewidth=2, markersize=6)
    plt.title(title, fontsize=14)
    plt.xlabel('# input Rules', fontsize=12)
    plt.ylabel(ylabel, fontsize=12)
    plt.grid(True, alpha=0.3)

    for x, y in zip(df[x_col], df[y_col]):
        if y_col == 'mat_size':
            amp = y / x if x > 0 else 0
            plt.annotate(f'{y}\n({amp:.1f}x)', (x, y), textcoords="offset points", 
                        xytext=(0,10), ha='center', fontsize=9)
        else:
            plt.annotate(f'{y:.3f}', (x, y), textcoords="offset points", 
                        xytext=(0,10), ha='center', fontsize=9)

    plt.tight_layout()
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    print(f"Plot saved to {output_file}")

def plot_combined_analysis(df, output_file="acl_combined.png"):
    _, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))

    # Runtime plot
    ax1.plot(df['count'], df['runtime'], 'bo-', linewidth=2, markersize=6)
    ax1.set_xlabel('# input Rules')
    ax1.set_ylabel('Runtime (ms)')
    ax1.grid(True, alpha=0.3)

    # Annotations runtime plot
    for x, y in zip(df['count'], df['runtime']):
        ax1.annotate(f'{y:.3f}', (x, y), textcoords="offset points", 
                    xytext=(0,10), ha='center', fontsize=9)

    # Table size plot with trend line
    ax2.plot(df['count'], df['mat_size'], 'ro-', linewidth=2, markersize=6)
    ax2.set_xlabel('# input rules')
    ax2.set_ylabel('Total output rules')
    ax2.grid(True, alpha=0.3)

    # Annotate table size plot
    for x, y in zip(df['count'], df['mat_size']):
        amp = y / x if x > 0 else 0
        ax2.annotate(f'{y}\n({amp:.1f}x)', (x, y), textcoords="offset points", 
                    xytext=(0,10), ha='center', fontsize=9)

    if len(df) > 1:
        z = np.polyfit(df['count'], df['mat_size'], 1)
        p = np.poly1d(z)
        ax2.plot(df['count'], p(df['count']), "r-", alpha=0.8, 
                label=f'Linear fit (slope={z[0]:.1f})')
        ax2.legend()

    plt.suptitle('ACL translation evaluation', fontsize=14)
    plt.tight_layout()
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    print(f"Combined plot saved to {output_file}")

def print_summary(df):
    amplifications = df['mat_size'] / df['count']
    rules_per_ms = df['count'] / df['runtime']
    print("Summary:")
    print(f"  Rule counts tested: {list(df['count'])}")
    print(f"  Runtime range: {df['runtime'].min():.3f}ms - {df['runtime'].max():.3f}ms")
    print(f"  Total output rules range: {df['mat_size'].min()} - {df['mat_size'].max()}")
    print(f"  Amplification factors: {[f'{amp:.1f}x' for amp in amplifications]}")
    print(f"  Average amplification: {amplifications.mean():.1f}x")
    print(f"  Processing rate: {rules_per_ms.min():.0f} - {rules_per_ms.max():.0f} rules/ms")

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 plot_acl_eval.py <csv_file_path>")
        sys.exit(1)

    csv_file = sys.argv[1]
    df = pd.read_csv(csv_file)

    print_summary(df)
    create_plot(df, 'count', 'runtime', 
                'ACL translation runtime vs. input rule count', 
                'Runtime (ms)', 'b', 'acl_runtime.png')
    create_plot(df, 'count', 'mat_size', 
                'ACL translation output rule count vs. input rule count', 
                'Total output rules', 'r', 'acl_mat_size.png')
    plot_combined_analysis(df)

if __name__ == "__main__":
    main()
