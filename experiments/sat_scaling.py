#!/usr/bin/env python3
"""Fixed finite-size protocol; work caps remain censored observations."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from pnp_lab.sat_scaling import (check_refutation, check_row_contradiction, dpll,
                                fit_growth, gaussian, graph_xor_cnf,
                                random_three_cnf, recognize_xor, satisfies)

PROTOCOL = {
    "version": "sat-scaling-v1",
    "replicates": 16,
    "literal_inspection_budget": 2_000_000,
    "xor_literal_inspection_budget": 8_000_000,
    "heuristics": ["first", "shortest"],
    "random_sizes": [12, 18, 24, 30, 36, 42, 48, 54, 60],
    "random_training_sizes": [12, 18, 24, 30, 36, 42],
    "xor_sizes": [12, 15, 18, 21, 24, 27, 30, 33],
    "xor_training_sizes": [12, 15, 18, 21, 24],
    "families": ["random_3sat_4.25", "random_3sat_6", "graph_xor_odd"],
    "pilot": "Excluded seed 19091+n at n=24,48,72; used only to set sizes and caps.",
    "seed_rule": "first 16 hex digits of SHA256(version:family:n:replicate)",
    "models": ["polynomial", "sqrt_exponential", "exponential"],
    "response": "log2(median literal inspections + 1)",
    "validation": "larger sizes held out; no model selected on training fit alone",
    "censoring": "UNKNOWN counts toward every summary; no fit if any size median is not exact",
    "meaning": "algorithm/distribution-specific empirical growth, not a probability of P vs NP",
}


def encoded(clauses):
    return json.dumps(clauses, separators=(",", ":")).encode()


def quantile_bound(records, numerator, denominator):
    """Nearest-rank order statistic; an unfinished run is >= its work cap."""
    values = sorted(records, key=lambda r: (r["literal_inspections"], r["status"] == "UNKNOWN"))
    index = (len(values) * numerator + denominator - 1) // denominator - 1
    record = values[index]
    return {"lower_bound": record["literal_inspections"], "exact": record["status"] != "UNKNOWN"}


def aggregate(records):
    groups = []
    for family in PROTOCOL["families"]:
        for heuristic in PROTOCOL["heuristics"]:
            sample = [r for r in records if r["family"] == family and r["heuristic"] == heuristic]
            summaries = []
            for n in sorted({r["n"] for r in sample}):
                rows = [r for r in sample if r["n"] == n]
                # Upper central order statistic (9th of 16) is a conservative,
                # fully specified median convention; do not mix conventions.
                median = quantile_bound(rows, len(rows) // 2 + 1, len(rows))
                summaries.append(dict(n=n, counts=dict(sorted(Counter(r["status"] for r in rows).items())),
                                      median=median, q25=quantile_bound(rows, 1, 4),
                                      q75=quantile_bound(rows, 3, 4),
                                      maximum_observed_work=max(r["literal_inspections"] for r in rows),
                                      median_nodes=statistics.median(r["nodes"] for r in rows),
                                      mean_dimacs_bytes=round(statistics.mean(r["dimacs_bytes"] for r in rows), 4)))
            train_count = 5 if family == "graph_xor_odd" else 6
            fits = sensitivity = None
            if all(s["median"]["exact"] for s in summaries):
                sizes = [s["n"] for s in summaries]
                costs = [s["median"]["lower_bound"] for s in summaries]
                fits = fit_growth(sizes, costs, train_count)
                # Same held-out sizes, discard two smallest training sizes.
                sensitivity = fit_growth(sizes[2:], costs[2:], train_count - 2)
            groups.append(dict(family=family, heuristic=heuristic, by_size=summaries,
                               fits=fits, window_sensitivity=sensitivity,
                               best_held_out_model=(min(fits, key=lambda k: fits[k]["held_out_log2_rmse"])
                                                    if fits else None),
                               fit_scope="finite median work of this DPLL algorithm on this generator"))
    return groups


def run():
    records = []
    algebraic = []
    for family in PROTOCOL["families"]:
        is_xor = family == "graph_xor_odd"
        sizes = PROTOCOL["xor_sizes" if is_xor else "random_sizes"]
        budget = PROTOCOL["xor_literal_inspection_budget" if is_xor else "literal_inspection_budget"]
        for n in sizes:
            for replicate in range(PROTOCOL["replicates"]):
                key = f'{PROTOCOL["version"]}:{family}:{n}:{replicate}'
                seed = int(hashlib.sha256(key.encode()).hexdigest()[:16], 16)
                if is_xor:
                    clauses = graph_xor_cnf(n, True, seed)
                else:
                    clauses = random_three_cnf(n, 17 if family.endswith("4.25") else 6,
                                               4 if family.endswith("4.25") else 1, seed)
                digest = hashlib.sha256(encoded(clauses)).hexdigest()
                dimacs = f"p cnf {n} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
                common = dict(family=family, n=n, clauses=len(clauses), replicate=replicate,
                              seed=seed, formula_sha256=digest, dimacs_bytes=len(dimacs.encode()))
                statuses = set()
                for heuristic in PROTOCOL["heuristics"]:
                    answer = dpll(n, clauses, heuristic, budget)
                    status = answer["status"]
                    if status == "SAT":
                        assert satisfies(clauses, answer["witness"])
                    elif status == "UNSAT":
                        assert check_refutation(n, clauses, answer["proof"])
                    else:
                        assert status == "UNKNOWN" and answer["literal_inspections"] == budget
                    if status != "UNKNOWN":
                        statuses.add(status)
                    assert len(statuses) <= 1
                    records.append(dict(**common, heuristic=heuristic, status=status,
                                        witness=answer["witness"], certificate_checked=status != "UNKNOWN",
                                        **{k: answer[k] for k in ("literal_inspections", "nodes", "decisions", "propagations")}))
                if is_xor:
                    equations = recognize_xor(n, clauses)
                    assert equations is not None
                    answer = gaussian(n, equations)
                    assert answer["status"] == "UNSAT"
                    assert check_row_contradiction(equations, answer["contradiction"])
                    assert not statuses or statuses == {"UNSAT"}
                    algebraic.append(dict(**common, status="UNSAT", equations=len(equations),
                                          row_xors=answer["row_xors"], rank=answer["rank"],
                                          certificate_checked=True))
            print(f"PASS {family} n={n}", flush=True)
    return dict(protocol=PROTOCOL, records=records, summaries=aggregate(records),
                algebraic_controls=algebraic,
                completed_dpll=sum(r["status"] != "UNKNOWN" for r in records),
                censored_dpll=sum(r["status"] == "UNKNOWN" for r in records),
                all_checks_passed=True, p_vs_np_resolved=False,
                p_vs_np_probability=None,
                scope="Observed solver/distribution growth only; no all-algorithm or all-size conclusion.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    report = run()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "sat_scaling.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: report[k] for k in ("completed_dpll", "censored_dpll", "scope")}))


if __name__ == "__main__":
    main()
