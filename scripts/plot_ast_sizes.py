#!/usr/bin/env python3

import matplotlib.pyplot as plt
from pathlib import Path

ITEMS = [
    (1, 6, "lo_ad"),                      
    (2, 7, "lo_ch"),
    (3, 6, "lo_db"),
    (4, 10, "lo_ev"),
    (5, 17, "lo_la"),
    (6, 6, "ad_lo"),
    (7, 13, "ad_ch"),
    (8, 12, "ad_db"),
    (9, 17, "ad_ev"),
    (10, 17, "ad_la"),
    (11, 3, "ch_lo"),
    (12, 6, "ch_ad"),
    (13, 6, "ch_db"),
    (14, 14, "ch_ev"),
    (15, 17, "ch_la"),
    (16, 3, "db_lo"),
    (17, 6, "db_ad"),
    (18, 7, "db_ch"),
    (19, 14, "db_ev"),
    (20, 17, "db_la"),
    (21, 8, "ev_lo"),
    (22, 11, "ev_ad"),
    (23, 17, "ev_ch"),
    (24, 16, "ev_db"),
    (25, 22, "ev_la"),
    (26, 15, "la_lo"),
    (27, 14, "la_ad"),
    (28, 31, "la_ch"),
    (29, 30, "la_db"),
    (30, 26, "la_ev"),
]

def main(save_path: str | None = None) -> None:
    x = [i for (i, _, _) in ITEMS]
    h = [v for (_, v, _) in ITEMS]
    labels = [lbl for (_, _, lbl) in ITEMS]

    _, ax = plt.subplots(figsize=(8, 3.5))
    ax.bar(x, h, width=0.7)

    # Add values above bars
    for xi, yi in zip(x, h):
        ax.text(xi, yi + 0.6, f"{yi}", ha="center", va="bottom", fontsize=8)

    # Labels & limits
    ax.set_ylabel("AST size")
    ax.set_xlim(0.5, max(x) + 0.5)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=8)

    # Horizontal dashed grid lines
    for yline in (5, 10, 15, 20, 25, 30):
        ax.axhline(yline, linestyle="--", linewidth=0.8)

    # Despine to look cleaner
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)

    plt.subplots_adjust(bottom=0.3, left=0.08, right=0.98, top=0.95)

    if save_path is None:
        save_path = Path(__file__).with_suffix(".png")
    else:
        save_path = Path(save_path)

    plt.savefig(save_path, dpi=200, bbox_inches="tight")
    print(f"Saved chart to {save_path}")

    try:
        import __main__
        plt.show()
    except Exception:
        pass

if __name__ == "__main__":
    main("ast-sizes.png")
