#!/usr/bin/env python3

import matplotlib.pyplot as plt
from matplotlib.ticker import LogLocator, LogFormatterMathtext
from pathlib import Path

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

def _compact_num(v: float) -> str:
    if v < 1000:
        return f"{int(v)}"
    elif v < 1e6:
        return f"{v/1000:.0f}K"
    else:
        return f"{v/1e6:.1f}M"

def main(save_path: str | None = None) -> None:
    labels = [k for (k, _) in DATA]
    values = [v for (_, v) in DATA]
    x = list(range(1, len(labels) + 1))

    _, ax = plt.subplots(figsize=(8, 3.5))
    ax.bar(x, values, width=0.7)

    ax.set_yscale("log")
    ax.yaxis.set_major_locator(LogLocator(base=10.0))
    ax.yaxis.set_major_formatter(LogFormatterMathtext(base=10.0))
    ax.yaxis.set_minor_locator(LogLocator(base=10.0, subs=[1.0, 2.0, 5.0]))
    ax.grid(True, which="both", axis="y", linestyle="--", linewidth=0.8, alpha=0.6)

    ax.set_ylabel("Runtime (µs)")
    ax.set_xlim(0.5, len(x) + 0.5)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=8)

    for xi, yi in zip(x, values):
        ax.text(
            xi, yi * 1.1, _compact_num(yi),
            ha="center", va="bottom", fontsize=7,
            rotation=0, rotation_mode="anchor"
        )

    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

    plt.subplots_adjust(bottom=0.3, left=0.08, right=0.98, top=0.95)

    if save_path is None:
        save_path = Path(__file__).with_suffix(".png")
    else:
        save_path = Path(save_path)

    plt.savefig(save_path, dpi=2400, bbox_inches='tight')
    print(f"Saved chart to {save_path}")

    try:
        import __main__
        plt.show()
    except Exception:
        pass

if __name__ == "__main__":
    main("compilation-times-bar.pdf")
