#!/usr/bin/env python3
"""Optional matplotlib figure of saved external-solver observations."""
import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=ROOT / "results/cdcl_audit.json")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    plt.rcParams.update({"font.size": 10, "svg.hashsalt": "cdcl-audit-v1"})
    fig, axes = plt.subplots(2, 3, figsize=(14, 8), constrained_layout=True)
    colors = {"g42": "#0072B2", "cadical195": "#D55E00"}
    names = {"g42": "Glucose 4.2.1", "cadical195": "CaDiCaL 1.9.5"}
    families = ["random_3sat_4.25", "random_3sat_6", "graph_xor_odd"]
    titles = ["Random 3-SAT: m=floor(4.25n)", "Random 3-SAT: m=6n", "Polynomial-time XOR control"]
    for col, (family, title) in enumerate(zip(families, titles)):
        groups = [g for g in report["summaries"] if g["panel"] == "extended" and g["family"] == family]
        for group in groups:
            solver = group["solver"]
            rows = group["by_size"]
            xs = [r["n"] for r in rows]
            ys = [max(1, r["median_conflicts"]["lower"]) for r in rows]
            ax = axes[0, col]
            exact_ys = [y if row["median_conflicts"]["exact"] else float("nan")
                        for y, row in zip(ys, rows)]
            ax.plot(xs, exact_ys, "-", color=colors[solver], label=names[solver])
            for x, y, row in zip(xs, ys, rows):
                bound = row["median_conflicts"]
                ax.plot(x, y, "o" if bound["exact"] else "^", color=colors[solver])
                if not bound["exact"]:
                    if bound["upper"] is not None:
                        ax.plot([x, x], [y, bound["upper"]], color=colors[solver], linestyle=":")
                    else:
                        ax.annotate("", (x, y * 1.55), (x, y),
                                    arrowprops={"arrowstyle": "->", "color": colors[solver]})
            rates = [(16 - r["counts"].get("UNKNOWN", 0)) / 16 for r in rows]
            axes[1, col].plot(xs, rates, "o-", color=colors[solver], label=names[solver])
        axes[0, col].set(title=title, ylabel="Native conflicts: upper-central median", yscale="log", xlabel="Variables n")
        top = max(r["median_conflicts"]["lower"] for g in groups for r in g["by_size"])
        axes[0, col].set_ylim(top=max(2, top * 2))
        axes[0, col].legend(fontsize=9)
        axes[1, col].set(ylabel="Fraction completed and checked", xlabel="Variables n", ylim=(-.03, 1.1))
        if family == "graph_xor_odd":
            axes[1, col].plot(xs, [1] * len(xs), "s--", color="#009E73", label="Gaussian elimination")
            axes[1, col].legend(fontsize=9, loc="lower left")
        for ax in axes[:, col]:
            ax.grid(alpha=.2)
    fig.suptitle("Practical CDCL audit: the XOR control remains polynomial-time solvable", fontsize=15)
    fig.supxlabel("16 instances per size; requested budget 25,000 conflicts (soft limit).\nTriangles/arrows: median bounds, not completed costs. Native counters are not wall time or DPLL literal visits.", fontsize=10)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.out_dir / "cdcl_audit.png", dpi=160)
    fig.savefig(args.out_dir / "cdcl_audit.svg", metadata={"Date": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
