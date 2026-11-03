#!/usr/bin/env python3
"""Reproduce checked CNF-to-XOR inferences and their structural limitations.

Cell counts are deterministic, not wall-clock benchmarks. Large search sizes
are explicitly marked as mathematical predictions; they are not enumerated.
"""

from __future__ import annotations

import argparse
from hashlib import sha256
from itertools import combinations
import json
from math import comb
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from pnp_lab.affine import AffineRelation
from pnp_lab.affine_hull import (
    check_cnf_coordinate_separation,
    coordinate_separation_certificate_for_leaf_cnf,
)
from pnp_lab.mixed import solve_mixed
from pnp_lab.parity_cuts import solve_with_parity_cuts, check_parity_cut_unsat_certificate
from pnp_lab.reductions import three_cnf_to_two_cnf_xor


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def scope(n):
    return tuple(f"x{i + 1}" for i in range(n))


def exactly_one(literals):
    literals = tuple(literals)
    return (literals,) + tuple((-a, -b) for a, b in combinations(literals, 2))


def exactly_two(n):
    variables = tuple(range(1, n + 1))
    lower = tuple(tuple(j for j in variables if j != i) for i in variables)
    upper = tuple(tuple(-j for j in triple) for triple in combinations(variables, 3))
    return lower + upper


def odd_cycle(n):
    require(n >= 3 and n % 2 == 1, "cycle must have odd length at least three")
    clauses = []
    for i in range(1, n + 1):
        j = i % n + 1
        clauses.extend(((i, j), (-i, -j)))
    return tuple(clauses)


def raw_cnf_holds(cnf, assignment):
    return all(any(((assignment >> (abs(lit) - 1)) & 1) == int(lit > 0)
                   for lit in clause) for clause in cnf)


def raw_models(n, rows, cnf):
    return [assignment for assignment in range(1 << n)
            if all(sum((assignment >> j) & 1 for j in range(n) if (mask >> j) & 1) % 2 == rhs
                   for mask, rhs in rows)
            and raw_cnf_holds(cnf, assignment)]


def solve(affine, cnf, *, exhaustive=False, max_cells=None, proof=False):
    return solve_with_parity_cuts(affine, cnf, exhaustive=exhaustive, max_cells=max_cells,
                                  include_trace=False, include_certificate=proof)


def short_result(result):
    fields = ("status", "reason", "affine_dimension", "effective_rank", "quotient_cells",
              "checked_cells", "model_count", "omitted_affine_directions")
    out = {key: result.get(key) for key in fields}
    prep = result["preprocessing"]
    out["preprocessing"] = {k: v for k, v in prep.items() if k != "derivation"}
    derivation = prep["derivation"]
    out["derivation_sha256"] = digest(derivation)
    out["exclusion_references"] = sum(len(c["exclusion_clauses"]) for c in derivation["cuts"])
    contradiction = derivation["contradiction"]
    out["contradiction_rows"] = len(contradiction["combination"]) if contradiction else None
    return out


def checked_linear_unsat(affine, cnf, result):
    require(result["status"] == "UNSAT" and result["checked_cells"] == 0,
            "expected a refutation without quotient enumeration")
    require(result["reason"] == "certified_linear_contradiction", "missing proof reason")
    require(check_parity_cut_unsat_certificate(affine, cnf, result["certificate"]),
            "linear UNSAT certificate rejected")


def run():
    old_family = []
    sample_unsat = None
    for n in (4, 8, 16, 32, 64, 128, 256):
        rows = (((1 << n) - 1, 0),)
        affine, cnf = AffineRelation(scope(n), rows), exactly_one(range(1, n + 1))
        result = solve(affine, cnf, max_cells=0, proof=True)
        checked_linear_unsat(affine, cnf, result)
        baseline_cells = None
        if n <= 16:
            baseline = solve_mixed(affine, cnf, exhaustive=False, include_trace=False)
            baseline_cells = baseline["checked_cells"]
            require(baseline["status"] == "UNSAT" and baseline_cells == 1 << (n - 1),
                    "baseline all-size formula disagrees with measured case")
        old_family.append({"n": n, "cnf_clauses": len(cnf), "baseline_cells_measured": baseline_cells,
                           "baseline_cells_predicted_decimal": str(1 << (n - 1)),
                           "solver": short_result(result), "proof_checked": True,
                           "checks_passed": True})
        if n == 4:
            sample_unsat = {"n_variables": n, "xor_rows": rows, "cnf": cnf,
                            "certificate": result["certificate"]}

    coupled = []
    for blocks in (2, 4, 8, 16, 32, 64):
        n = 3 * blocks
        cnf = sum((exactly_one(range(3 * i + 1, 3 * i + 4)) for i in range(blocks)), ())
        affine = AffineRelation(scope(n), (((1 << n) - 1, 1 ^ (blocks % 2)),))
        result = solve(affine, cnf, max_cells=0, proof=True)
        checked_linear_unsat(affine, cnf, result)
        require(result["preprocessing"]["derived_cut_count"] == blocks, "one cut per block")
        require(len(result["preprocessing"]["derivation"]["contradiction"]["combination"]) == blocks + 1,
                "global contradiction must combine all blocks with the input row")
        coupled.append({"blocks": blocks, "n": n, "cnf_clauses": len(cnf),
                        "solver": short_result(result), "proof_checked": True, "checks_passed": True})

    sat_controls = []
    for blocks in (1, 2, 3, 4):
        n = 3 * blocks
        cnf = sum((exactly_one(range(3 * i + 1, 3 * i + 4)) for i in range(blocks)), ())
        affine = AffineRelation(scope(n), (((1 << n) - 1, blocks % 2),))
        result = solve(affine, cnf, exhaustive=True)
        before = solve_mixed(affine, cnf, exhaustive=True, include_trace=False)
        require(result["status"] == "SAT" and result["model_count"] == 3 ** blocks,
                "exactly-one block models were not preserved")
        require(before["model_count"] == result["model_count"], "model counts changed")
        require(result["affine_dimension"] == result["effective_rank"] == 2 * blocks,
                "strengthened block rank")
        require(before["omitted_affine_directions"] == result["omitted_affine_directions"],
                "unobserved directions must be preserved")
        sat_controls.append({"blocks": blocks, "n": n, "expected_models": 3 ** blocks,
                             "baseline_cells": before["checked_cells"], "solver": short_result(result),
                             "checks_passed": True})

    two_barrier = []
    for n in (4, 6, 8, 10, 12, 14, 16):
        cnf = exactly_two(n)
        affine = AffineRelation(scope(n), (((1 << n) - 1, 1),))
        result = solve(affine, cnf, proof=n == 4)
        require(result["status"] == "UNSAT" and result["checked_cells"] == 1 << (n - 1),
                "exact-two barrier did not enumerate all cells")
        require(result["preprocessing"]["derived_cut_count"] == 0, "unexpected exact-two cut")
        require(result["affine_dimension"] == result["effective_rank"] == n - 1,
                "exact-two rank")
        cnf_models = None
        if n <= 10:
            cnf_models = sum(raw_cnf_holds(cnf, a) for a in range(1 << n))
            require(cnf_models == comb(n, 2), "independent exact-two semantics")
            require(not raw_models(n, affine.equations, cnf), "independent mixed UNSAT")
        if n == 4:
            require(check_parity_cut_unsat_certificate(affine, cnf, result["certificate"]),
                    "residual enumeration certificate failed")
        two_barrier.append({"n": n, "cnf_clauses": len(cnf), "cnf_only_models_measured": cnf_models,
                            "cnf_only_models_predicted": comb(n, 2), "solver": short_result(result),
                            "checks_passed": True})

    encoding_cases = []
    sample_hull = None
    for k in (3, 5, 11, 33, 101):
        source = odd_cycle(k)
        original = AffineRelation.truth(scope(k))
        direct = solve(original, source, max_cells=0, proof=True)
        checked_linear_unsat(original, source, direct)
        bridge = three_cnf_to_two_cnf_xor(scope(k), source)
        n = len(bridge.affine.variables)
        require(n == 7 * k and len(bridge.cnf) == 6 * k, "bridge sizes")
        transformed = solve(bridge.affine, bridge.cnf, max_cells=None if k == 3 else 32)
        require(transformed["preprocessing"]["derived_cut_count"] == 0, "bridge cannot yield cuts")
        require(transformed["affine_dimension"] == transformed["effective_rank"] == 5 * k,
                "bridge image keeps all affine directions observable")
        require(transformed["checked_cells"] == (1 << (5 * k) if k == 3 else 32), "search count")
        require(transformed["status"] == ("UNSAT" if k == 3 else "UNKNOWN"), "budget status")
        hull = coordinate_separation_certificate_for_leaf_cnf(n, k, bridge.cnf)
        require(check_cnf_coordinate_separation(n, bridge.cnf, hull), "full-hull certificate")
        encoding_cases.append({
            "cycle_length": k, "source_variables": k, "source_clauses": len(source),
            "target_variables": n, "target_binary_clauses": len(bridge.cnf),
            "direct_solver": short_result(direct), "bridge_solver": short_result(transformed),
            "bridge_full_search_cells_predicted_decimal": str(1 << (5 * k)),
            "bridge_full_search_completed": k == 3,
            "full_hull_certificate_checked": True, "cnf_affine_hull_dimension": n,
            "full_hull_coordinate_pairs": len(hull["pairs"]), "full_hull_certificate_sha256": digest(hull),
            "checks_passed": True,
        })
        if k == 3:
            sample_hull = {"n_variables": n, "cnf": bridge.cnf, "certificate": hull}

    rng = random.Random(2026110403)
    oracle_cases = []
    total_assignments = 0
    for case in range(160):
        n = 1 + case % 8
        variables = list(range(1, n + 1))
        rng.shuffle(variables)
        literals = tuple(v * rng.choice((-1, 1)) for v in variables[:rng.randint(1, n)])
        cnf = exactly_one(literals)
        cnf += tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                           for _ in range(rng.randint(0, 4))) for _ in range(rng.randint(0, 4)))
        rows = tuple((rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(4)))
        models = raw_models(n, rows, cnf)
        total_assignments += 1 << n
        affine = AffineRelation(scope(n), rows)
        before = solve_mixed(affine, cnf, exhaustive=True, include_trace=False)
        after = solve(affine, cnf, exhaustive=True, proof=True)
        require(before["model_count"] == after["model_count"] == len(models), "raw oracle disagreement")
        require(after["status"] == ("SAT" if models else "UNSAT"), "raw oracle status")
        proof_checked = None
        if models:
            require(after["witness_mask"] in models, "invalid original-input witness")
        else:
            proof_checked = check_parity_cut_unsat_certificate(affine, cnf, after["certificate"])
            require(proof_checked, "oracle case proof failed")
        prep = after["preprocessing"]
        invariant = None
        if not prep["contradiction_found"]:
            invariant = (before["omitted_affine_directions"] == after["omitted_affine_directions"]
                         and before["affine_dimension"] - after["affine_dimension"]
                         == before["effective_rank"] - after["effective_rank"])
            require(invariant, "rank-drop invariant failed")
        oracle_cases.append({"case": case, "n": n, "input_sha256": digest([rows, cnf]),
                             "models": len(models), "status": after["status"],
                             "derived_cuts": prep["derived_cut_count"],
                             "baseline_cells": before["checked_cells"], "new_cells": after["checked_cells"],
                             "rank_drop_invariant": invariant, "unsat_proof_checked": proof_checked,
                             "checks_passed": True})

    report = {
        "schema_version": 1, "all_checks_passed": True,
        "scope": "Checked exactly-one parity strengthening; not a P versus NP solution or a new general lower bound.",
        "counting_note": "checked_cells excludes polynomial preprocessing. Predictions for unenumerated sizes are explicitly labeled.",
        "algorithm_general_polynomial_time": False,
        "exactly_one_even_cases": old_family, "coupled_block_cases": coupled,
        "satisfiable_controls": sat_controls, "exactly_two_odd_barrier_cases": two_barrier,
        "encoding_cases": encoding_cases,
        "independent_oracle": {"seed": 2026110403, "case_count": len(oracle_cases),
                               "original_assignments_checked": total_assignments, "cases": oracle_cases},
        "sample_linear_unsat_proof": sample_unsat, "sample_full_hull_proof": sample_hull,
        "summary": {
            "largest_exactly_one_variables": max(c["n"] for c in old_family),
            "largest_coupled_variables": max(c["n"] for c in coupled),
            "largest_exact_two_measured_cells": max(c["solver"]["checked_cells"] for c in two_barrier),
            "bridge_cycle3_measured_cells": encoding_cases[0]["bridge_solver"]["checked_cells"],
            "largest_full_hull_dimension_certified": max(c["cnf_affine_hull_dimension"] for c in encoding_cases),
            "oracle_cases": len(oracle_cases), "oracle_original_assignments_checked": total_assignments,
            "oracle_sat": sum(c["status"] == "SAT" for c in oracle_cases),
            "oracle_unsat": sum(c["status"] == "UNSAT" for c in oracle_cases),
            "rank_invariant_cases": sum(c["rank_drop_invariant"] is True for c in oracle_cases),
        },
    }
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    report = run()
    path = args.out_dir / "parity_cuts.json"
    path.write_text(json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": report["all_checks_passed"], **report["summary"]}, indent=2))


if __name__ == "__main__":
    main()
