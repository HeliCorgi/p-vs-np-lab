"""Stdlib helpers for optional, independently proof-checked CDCL experiments."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from .sat_scaling import fit_growth, graph_xor_cnf, random_three_cnf, satisfies


def formula_hash(clauses):
    return hashlib.sha256(json.dumps(clauses, separators=(",", ":")).encode()).hexdigest()


def regenerate(family, n, seed):
    if family == "graph_xor_odd":
        return graph_xor_cnf(n, True, seed)
    if family == "random_3sat_4.25":
        return random_three_cnf(n, 17, 4, seed)
    if family == "random_3sat_6":
        return random_three_cnf(n, 6, 1, seed)
    raise ValueError("unrecognized formula family")


def dimacs(n, clauses):
    return f"p cnf {n} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)


def checked_model(n, clauses, model):
    if model is None:
        raise ValueError("missing SAT model")
    assignment = {}
    for lit in model:
        if type(lit) is not int or not 1 <= abs(lit) <= n:
            raise ValueError("model has invalid literals")
        if abs(lit) in assignment and assignment[abs(lit)] != (lit > 0):
            raise ValueError("inconsistent model")
        assignment[abs(lit)] = lit > 0
    word = sum(1 << (v - 1) for v, bit in assignment.items() if bit)
    if not satisfies(clauses, word):
        raise ValueError("model falsifies an original clause")
    return word


def verified_output(returncode, stdout):
    return returncode == 0 and "s VERIFIED" in [line.strip() for line in stdout.splitlines()]


def verify_drat(checker, cnf_path, proof_path, log_path):
    result = subprocess.run([str(checker), str(cnf_path), str(proof_path)],
                            text=True, capture_output=True, timeout=30)
    Path(log_path).write_text(result.stdout + result.stderr)
    if not verified_output(result.returncode, result.stdout):
        raise RuntimeError(f"DRAT verification failed; see {log_path}")


def verify_checker_source(root):
    directory = Path(root) / "third_party/drat_trim"
    manifest = json.loads((directory / "manifest.json").read_text())
    if manifest["commit"] != "2e3b2dc0ecf938addbd779d42877b6ed69d9a985" or manifest["license"] != "MIT":
        raise ValueError("unexpected checker pin/license")
    if {r["path"] for r in manifest["files"]} != {"drat-trim.c", "LICENSE"}:
        raise ValueError("unexpected checker file set")
    for record in manifest["files"]:
        data = (directory / record["path"]).read_bytes()
        if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
            raise ValueError("checker snapshot changed")
    return manifest


def order_statistic_bounds(records, index, counter="conflicts"):
    """1-based rank with variable right-censoring thresholds; no dropped runs."""
    if not 1 <= index <= len(records):
        raise ValueError("invalid order statistic")
    lower = sorted(r[counter] for r in records)[index - 1]
    finite_upper = sorted(r[counter] for r in records if r["status"] != "UNKNOWN")
    upper = finite_upper[index - 1] if len(finite_upper) >= index else None
    return dict(lower=lower, upper=upper, exact=upper is not None and lower == upper)


def summarize(records):
    summaries = []
    keys = sorted({(r["panel"], r["family"], r["solver"]) for r in records})
    for panel, family, solver in keys:
        rows = [r for r in records if (r["panel"], r["family"], r["solver"]) == (panel, family, solver)]
        sizes = []
        for n in sorted({r["n"] for r in rows}):
            sample = [r for r in rows if r["n"] == n]
            sizes.append(dict(n=n, counts=dict(sorted(Counter(r["status"] for r in sample).items())),
                              median_conflicts=order_statistic_bounds(sample, len(sample) // 2 + 1),
                              minimum_conflicts=min(r["conflicts"] for r in sample),
                              maximum_observed_conflicts=max(r["conflicts"] for r in sample),
                              maximum_observed_propagations=max(r["propagations"] for r in sample)))
        fits = sensitivity = None
        if panel == "extended" and all(s["median_conflicts"]["exact"] for s in sizes):
            ns = [s["n"] for s in sizes]
            costs = [s["median_conflicts"]["lower"] for s in sizes]
            fits = fit_growth(ns, costs, 3)
            sensitivity = fit_growth(ns[1:], costs[1:], 2)
        summaries.append(dict(panel=panel, family=family, solver=solver, by_size=sizes,
                              fits=fits, training_window_sensitivity=sensitivity,
                              best_held_out_model=(min(fits, key=lambda k: fits[k]["held_out_log2_rmse"])
                                                   if fits else None)))
    return summaries
