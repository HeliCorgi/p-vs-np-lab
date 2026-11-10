#!/usr/bin/env python3
"""Optional visualization of the saved audit (requires matplotlib only here)."""
import argparse
import json
import math
from pathlib import Path
import statistics

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=ROOT / "results/sat_scaling.json")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    plt.rcParams.update({"font.size": 10, "svg.hashsalt": "sat-scaling-v1"})
    fig, axes = plt.subplots(2, 2, figsize=(12, 8), constrained_layout=True)
    colors = {"first": "#0072B2", "shortest": "#D55E00"}
    features = {"polynomial": math.log2, "exponential": float, "sqrt_exponential": math.sqrt}
    titles = ["Random 3-SAT, m=floor(4.25n)", "Random 3-SAT, m=6n",
              "Known tractable XOR control: DPLL", "Same XOR CNFs: recovered Gaussian elimination"]
    for ax, family, title in zip(axes.flat, report["protocol"]["families"], titles):
        groups = [g for g in report["summaries"] if g["family"] == family]
        for group in groups:
            color = colors[group["heuristic"]]
            summaries = group["by_size"]
            ns = [s["n"] for s in summaries]
            ys = [s["median"]["lower_bound"] for s in summaries]
            ax.plot(ns, ys, "o-", color=color, label=group["heuristic"] + " DPLL")
            ax.fill_between(ns, [s["q25"]["lower_bound"] for s in summaries],
                            [s["q75"]["lower_bound"] for s in summaries], color=color, alpha=.12)
            for n, s in zip(ns, summaries):
                if not s["median"]["exact"]:
                    y = s["median"]["lower_bound"]
                    ax.annotate("capped", (n, y), xytext=(n, 1.5 * y), color=color,
                                ha="center", fontsize=8, arrowprops={"arrowstyle": "->", "color": color})
            if group["fits"]:
                model = group["best_held_out_model"]
                fit = group["fits"][model]
                training = 5 if family == "graph_xor_odd" else 6
                holdout = ns[training:]
                predictions = [2 ** (fit["intercept"] + fit["slope"] * features[model](n)) - 1 for n in holdout]
                ax.plot(holdout, predictions, "x--", color=color, alpha=.8)
        training = 5 if family == "graph_xor_odd" else 6
        sizes = groups[0]["by_size"]
        boundary = (sizes[training - 1]["n"] + sizes[training]["n"]) / 2
        ax.axvspan(boundary, sizes[-1]["n"] + 1, color="gray", alpha=.08)
        ax.set(title=title, xlabel="Variables n", ylabel="Literal inspections (log scale)", yscale="log")
        ax.grid(alpha=.2)
        ax.legend(loc="upper left", fontsize=8)
    ax = axes[1, 1]
    controls = report["algebraic_controls"]
    ns = sorted({r["n"] for r in controls})
    medians = [statistics.median(r["row_xors"] for r in controls if r["n"] == n) for n in ns]
    ax.plot(ns, medians, "o-", color="#009E73", label="Gaussian row XORs")
    ax.set(title=titles[3], xlabel="Variables n", ylabel="Row XORs (different unit from other panels)")
    ax.grid(alpha=.2)
    ax.legend(loc="upper left", fontsize=8)
    ax.text(.03, .64, "All 128 UNSAT certificates checked.\nEquations recovered from CNF.\nNo hidden graph metadata.\nPolynomial bit-time algorithm.",
            transform=ax.transAxes, fontsize=10, va="top")
    fig.suptitle("Finite-size SAT audit: growth of specified solvers, not a P vs NP verdict", fontsize=15)
    fig.supxlabel("16 instances per size. Shading: 25th-75th ranks; gray: held-out sizes.\nDashed x: best held-out model prediction. Capped bands are lower bounds.", fontsize=10)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.out_dir / "sat_scaling.png", dpi=160)
    fig.savefig(args.out_dir / "sat_scaling.svg", metadata={"Date": None})
    plt.close(fig)


if __name__ == "__main__":
    main()
