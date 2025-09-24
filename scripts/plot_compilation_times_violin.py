#!/usr/bin/env python3

import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator, LogFormatterMathtext
import numpy as np

DATA = [
    ("lo_ad", 694.0),                     
    ("lo_ch", 2.0),
    ("lo_db", 2.0),
    ("lo_ev", 5.0),
    ("lo_la", 61959.0),
    ("ad_lo", 55249.0),
    ("ad_ch", 105793.0),
    ("ad_db", 105043.0),
    ("ad_ev", 57649.0),
    ("ad_la", 60334.0),
    ("ch_lo", 2.0),
    ("ch_ad", 834.0),
    ("ch_db", 1.0),
    ("ch_ev", 6.0),
    ("ch_la", 61226.0),
    ("db_lo", 1.0),
    ("db_ad", 983.0),
    ("db_ch", 2.0),
    ("db_ev", 5.0),
    ("db_la", 62475.0),
    ("ev_lo", 10.0),
    ("ev_ad", 993.0),
    ("ev_ch", 9.0),
    ("ev_db", 10.0),
    ("ev_la", 61712.0),
    ("la_lo", 71753.0),
    ("la_ad", 21279.0),
    ("la_ch", 160040.0),
    ("la_db", 148079.0),
    ("la_ev", 72272.0),    
]

COLOR_MAP = {
    "lo": "#1f77b4",  # blue
    "ad": "#ff7f0e",  # orange
    "ch": "#2ca02c",  # green
    "db": "#d62728",  # red
    "ev": "#9467bd",  # purple
    "la": "#8c564b",  # brown
}

def group_by_source(data):
    """Return dict: source -> list of (target, runtime)."""
    groups = {}
    for name, val in data:
        src, dst = name.split("_", 1)
        groups.setdefault(src, []).append((dst, float(val)))
    return groups

def plot_violin(save_path):
    groups = group_by_source(DATA)
    order = ["lo", "ad", "ch", "db", "ev", "la"]

    values_in_order = [[v for (_, v) in groups[src]] for src in order]

    fig, ax = plt.subplots(figsize=(7.0, 3.8))

    # Draw violins
    parts = ax.violinplot(
        values_in_order,
        positions=np.arange(1, len(order) + 1),
        showmedians=True,
        widths=0.8
    )
    for pc in parts["bodies"]:
        pc.set_facecolor("lightgray")
        pc.set_edgecolor("black")
        pc.set_alpha(0.4)

    for key in ("cmedians", "cmins", "cmaxes", "cbars"):
        if key in parts:
            parts[key].set_linewidth(1.0)

    # Overlay scatter points colored by target pipeline
    rng = np.random.default_rng(0)
    for i, src in enumerate(order, start=1):
        for dst, val in groups[src]:
            jitter_x = i + rng.uniform(-0.08, 0.08)
            ax.scatter(
                jitter_x, val,
                s=18, alpha=0.9,
                color=COLOR_MAP[dst],
                edgecolor="black", linewidth=0.3
            )

    ax.set_yscale("log")
    ax.yaxis.set_major_locator(LogLocator(base=10.0))
    ax.yaxis.set_major_formatter(LogFormatterMathtext(base=10.0))
    ax.yaxis.set_minor_locator(LogLocator(base=10.0, subs=[1.0, 2.0, 5.0], numticks=12))
    ax.grid(True, which="both", axis="y", linestyle="--", linewidth=0.8, alpha=0.6)

    ax.set_ylabel("Runtime (µs)")
    ax.set_xlim(0.5, len(order) + 0.5)
    ax.set_xticks(range(1, len(order) + 1))
    ax.set_xticklabels(order, fontsize=9)

    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    fig.tight_layout()

    # Legend for target pipeline colors
    handles = [
        plt.Line2D([0], [0], marker="o", color="w", label=dst,
                   markerfacecolor=COLOR_MAP[dst], markeredgecolor="black", markersize=7)
        for dst in order
    ]
    ax.legend(handles=handles, title="Target pipeline", loc="upper left", bbox_to_anchor=(1.02, 1.0))

    fig.savefig(save_path, dpi=2400, bbox_inches='tight')
    print(f"Saved violin plot to {save_path}")

if __name__ == "__main__":
    plot_violin("compilation-times-violin.pdf")
