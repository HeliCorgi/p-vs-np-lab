#!/usr/bin/env python3
"""Reproduce checked joint XOR/binary inference and its remaining barriers.

Only representative counts are reported, not timing benchmarks. The previous
32768-cell bridge measurement is read from its checked-in result; larger old
search sizes are mathematical predictions and are never enumerated here.
"""

from __future__ import annotations

import argparse
from hashlib import sha256
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from pnp_lab.affine import AffineRelation
from pnp_lab.joint import (
    check_joint_clause_certificate,
    check_joint_unsat_certificate,
    solve_with_joint_reasoning,
)
from pnp_lab.mixed import solve_mixed
from pnp_lab.reductions import three_cnf_to_two_cnf_xor


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(value):
    return sha256(encoded(value)).hexdigest()


def scope(n):
    return tuple(f"x{i + 1}" for i in range(n))


def odd_cycle(n):
    require(n >= 3 and n % 2 == 1, "cycle must have odd length at least three")
    return tuple(clause for i in range(1, n + 1)
                 for clause in ((i, i % n + 1), (-i, -(i % n + 1))))


def exactly_two(n):
    variables = tuple(range(1, n + 1))
    return (tuple(tuple(j for j in variables if j != i) for i in variables)
            + tuple(tuple(-j for j in triple) for triple in combinations(variables, 3)))


def raw_cnf_holds(cnf, assignment):
    return all(any(((assignment >> (abs(lit) - 1)) & 1) == int(lit > 0)
                   for lit in clause) for clause in cnf)


def raw_models(n, rows, cnf):
    """Read raw rows and literal signs without solver normalization helpers."""
    return {assignment for assignment in range(1 << n)
            if all(sum((assignment >> j) & 1 for j in range(n) if (mask >> j) & 1) % 2 == rhs
                   for mask, rhs in rows) and raw_cnf_holds(cnf, assignment)}


def parity_cnf(columns, rhs):
    return tuple(tuple(-(column + 1) if value else column + 1
                       for column, value in zip(columns, forbidden))
                 for forbidden in product((0, 1), repeat=len(columns))
                 if sum(forbidden) % 2 != rhs)


def prism_formula(k):
    """One native odd vertex, all other even vertex parities encoded as 3CNF."""
    require(k >= 3, "simple prism requires k >= 3")
    vertices = [(i, (i - 1) % k, 2 * k + i) for i in range(k)]
    vertices += [(k + i, k + (i - 1) % k, 2 * k + i) for i in range(k)]
    row = (sum(1 << column for column in vertices[0]), 1)
    cnf = sum((parity_cnf(columns, 0) for columns in vertices[1:]), ())
    require(all(len(set(columns)) == 3 for columns in vertices), "vertex is not cubic")
    require(all(sum(column in vertex for vertex in vertices) == 2 for column in range(3 * k)),
            "each edge must occur at exactly two vertices")
    require({abs(lit) for clause in cnf for lit in clause} == set(range(1, 3 * k + 1)),
            "all affine variables must be observable in the CNF")
    return (row,), cnf


def solve(affine, cnf, *, exhaustive=False, max_cells=None, proof=False):
    return solve_with_joint_reasoning(
        affine, cnf, exhaustive=exhaustive, max_cells=max_cells,
        include_trace=False, include_certificate=proof,
    )


def short_result(result):
    fields = ("status", "reason", "affine_dimension", "effective_rank", "quotient_cells",
              "checked_cells", "model_count", "omitted_affine_directions")
    out = {key: result.get(key) for key in fields}
    for key in ("joint_preprocessing", "preprocessing"):
        out[key] = {field: value for field, value in result[key].items() if field != "derivation"}
        out[key]["derivation_sha256"] = digest(result[key]["derivation"])
    proof = result.get("certificate")
    out["certificate_sha256"] = digest(proof) if proof is not None else None
    out["certificate_bytes"] = len(encoded(proof)) if proof is not None else None
    return out


def previous_bridge_baseline():
    path = ROOT / "results" / "parity_cuts.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    require(data["all_checks_passed"] is True, "previous report was not successful")
    case = next(item for item in data["encoding_cases"] if item["cycle_length"] == 3)
    require(case["bridge_full_search_completed"] is True
            and case["bridge_solver"]["status"] == "UNSAT"
            and case["bridge_solver"]["checked_cells"] == 32768,
            "previous bridge baseline differs from the reported measurement")
    return {"source": "results/parity_cuts.json", "cycle_length": 3,
            "previously_measured_cells": 32768, "rerun_in_this_experiment": False,
            "source_file_sha256": sha256(path.read_bytes()).hexdigest(),
            "source_case_sha256": digest(case)}


def run():
    prior = previous_bridge_baseline()
    cycles = []
    sample_proof = None
    for k in (3, 5, 11, 33, 101):
        source = odd_cycle(k)
        bridge = three_cnf_to_two_cnf_xor(scope(k), source)
        result = solve(bridge.affine, bridge.cnf, max_cells=0, proof=True)
        require(result["status"] == "UNSAT" and result["checked_cells"] == 0,
                "bridge cycle was not refuted during preprocessing")
        require(result["reason"] == "certified_linear_contradiction", "missing parity proof")
        require(check_joint_unsat_certificate(bridge.affine, bridge.cnf, result["certificate"]),
                "composed bridge proof rejected against original input")
        derived = result["joint_preprocessing"]["derivation"]["clauses"]
        require({tuple(step["clause"]) for step in derived}
                == {tuple(sorted(clause, key=lambda lit: (abs(lit), lit))) for clause in source},
                "joint inference did not recover exactly the source clauses")
        require(result["joint_preprocessing"]["candidates_examined"] == 2 * k,
                "unexpected number of bridge premise choices")
        require(len(bridge.affine.variables) == 7 * k and len(bridge.cnf) == 6 * k,
                "unexpected bridge size")
        cycles.append({
            "cycle_length": k, "source_clauses": 2 * k, "target_variables": 7 * k,
            "target_binary_clauses": 6 * k, "target_xor_rows": 2 * k,
            "baseline_affine_dimension_predicted": 5 * k,
            "baseline_cells_predicted_decimal": str(1 << (5 * k)),
            "baseline_cells_measured_previously": 32768 if k == 3 else None,
            "baseline_search_rerun": False,
            "solver": short_result(result), "original_input_proof_checked": True,
            "checks_passed": True,
        })
        if k == 3:
            sample_proof = {"n_variables": len(bridge.affine.variables),
                            "xor_rows": bridge.affine.equations, "cnf": bridge.cnf,
                            "certificate": result["certificate"]}

    two_barrier = []
    for n in (4, 6, 8, 10, 12, 14, 16):
        rows, cnf = (((1 << n) - 1, 1),), exactly_two(n)
        affine = AffineRelation(scope(n), rows)
        result = solve(affine, cnf, proof=n == 4)
        require(result["status"] == "UNSAT" and result["checked_cells"] == 1 << (n - 1),
                "exactly-two family did not retain its predicted full search")
        require(result["joint_preprocessing"]["derived_clause_count"] == 0
                and result["preprocessing"]["derived_cut_count"] == 0, "unexpected barrier inference")
        require(result["affine_dimension"] == result["effective_rank"] == n - 1,
                "exactly-two family lost an observed direction")
        limited = solve(affine, cnf, max_cells=0)
        require(limited["status"] == "UNKNOWN", "zero budget must leave this barrier unknown")
        if n == 4:
            require(check_joint_unsat_certificate(affine, cnf, result["certificate"]),
                    "residual barrier proof rejected")
        cnf_models = None
        if n <= 8:
            cnf_models = len(raw_models(n, (), cnf))
            require(cnf_models == comb(n, 2) and not raw_models(n, rows, cnf),
                    "raw exactly-two semantics disagree")
        two_barrier.append({"n": n, "cnf_clauses": len(cnf),
                            "cnf_only_models_predicted": comb(n, 2),
                            "cnf_only_models_measured": cnf_models,
                            "solver": short_result(result), "zero_budget_status": limited["status"],
                            "checks_passed": True})

    prisms = []
    for k in (3, 4, 5):
        n = 3 * k
        rows, cnf = prism_formula(k)
        affine = AffineRelation(scope(n), rows)
        result = solve(affine, cnf)
        require(result["status"] == "UNSAT" and result["checked_cells"] == 1 << (n - 1),
                "prism family did not retain its predicted full search")
        require(result["joint_preprocessing"]["candidates_examined"] == 0
                and result["preprocessing"]["derived_cut_count"] == 0, "unexpected prism inference")
        require(result["affine_dimension"] == result["effective_rank"] == n - 1,
                "prism family lost an observed direction")
        require(raw_cnf_holds(cnf, 0), "CNF component should have its zero model")
        if k == 3:
            require(not raw_models(n, rows, cnf), "raw prism semantics disagree")
        prisms.append({"cycle_length": k, "graph_vertices": 2 * k,
                       "n": n, "cnf_clauses": len(cnf), "native_xor_rows": 1,
                       "all_constraint_arities": 3, "cnf_component_zero_model_checked": True,
                       "solver": short_result(result), "checks_passed": True})

    single = three_cnf_to_two_cnf_xor(scope(3), ((1, 2, 3),))
    single_result = solve(single.affine, single.cnf, exhaustive=True)
    single_models = raw_models(6, single.affine.equations, single.cnf)
    require(len(single_models) == single_result["model_count"] == 13,
            "joint inference must preserve target counts, not source counts")
    require(single_result["witness_mask"] in single_models, "SAT control has invalid witness")
    control = {"source_models": 7, "original_target_models": 13,
               "solver": short_result(single_result), "checks_passed": True}

    rng = random.Random(2026110404)
    oracle_cases = []
    total_assignments = 0
    for case in range(160):
        n = 1 + case % 7
        rows = tuple((rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(4)))
        cnf = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                          for _ in range(rng.randrange(5))) for _ in range(rng.randrange(7)))
        if n >= 2 and case % 2 == 0:
            width = min(3, n - 1)
            rows += (((1 << width) - 1, rng.randrange(2)),)
            cnf += tuple((rng.choice((-1, 1)) * (i + 1),
                          rng.choice((-1, 1)) * rng.randint(width + 1, n)) for i in range(width))
        models = raw_models(n, rows, cnf)
        total_assignments += 1 << n
        affine = AffineRelation(scope(n), rows)
        before = solve_mixed(affine, cnf, exhaustive=True, include_trace=False)
        after = solve(affine, cnf, exhaustive=True, proof=True)
        require(before["model_count"] == after["model_count"] == len(models), "raw model count mismatch")
        require(after["status"] == ("SAT" if models else "UNSAT"), "raw decision mismatch")
        derivation = after["joint_preprocessing"]["derivation"]
        require(check_joint_clause_certificate(affine, cnf, derivation), "oracle derivation rejected")
        augmented = cnf + tuple(tuple(step["clause"]) for step in derivation["clauses"])
        require(raw_models(n, rows, augmented) == models, "joint clauses changed the model set")
        proof_checked = None
        if models:
            require(after["witness_mask"] in models, "oracle witness invalid on original input")
        else:
            proof_checked = check_joint_unsat_certificate(affine, cnf, after["certificate"])
            require(proof_checked, "oracle composed proof rejected")
        oracle_cases.append({"case": case, "n": n, "input_sha256": digest([rows, cnf]),
                             "models": len(models), "status": after["status"],
                             "joint_clauses": len(derivation["clauses"]),
                             "parity_cuts": after["preprocessing"]["derived_cut_count"],
                             "baseline_cells": before["checked_cells"], "new_cells": after["checked_cells"],
                             "joint_derivation_sha256": digest(derivation),
                             "original_models_preserved": True, "unsat_proof_checked": proof_checked,
                             "checks_passed": True})

    return {
        "schema_version": 1, "all_checks_passed": True,
        "scope": "One-pass fixed-width-three joint inference; general exponential residual families remain.",
        "counting_note": "checked_cells excludes polynomial preprocessing; old unenumerated counts are predictions.",
        "algorithm_general_polynomial_time": False,
        "previous_baseline": prior,
        "bridge_odd_cycle_cases": cycles,
        "exactly_two_odd_barrier_cases": two_barrier,
        "prism_tseitin_barrier_cases": prisms,
        "non_parsimonious_bridge_control": control,
        "independent_oracle": {"seed": 2026110404, "case_count": len(oracle_cases),
                               "original_assignments_checked": total_assignments, "cases": oracle_cases},
        "sample_composed_unsat_proof": sample_proof,
        "summary": {
            "oracle_cases": len(oracle_cases),
            "oracle_original_assignments_checked": total_assignments,
            "oracle_sat": sum(case["status"] == "SAT" for case in oracle_cases),
            "oracle_unsat": sum(case["status"] == "UNSAT" for case in oracle_cases),
            "largest_zero_cell_cycle": max(case["cycle_length"] for case in cycles),
            "largest_zero_cell_target_variables": max(case["target_variables"] for case in cycles),
            "largest_barrier_cells": max(case["solver"]["checked_cells"] for case in two_barrier + prisms),
            "largest_prism_variables": max(case["n"] for case in prisms),
            "prior_cycle3_baseline_cells": prior["previously_measured_cells"],
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    report = run()
    path = args.out_dir / "joint_reasoning.json"
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": report["all_checks_passed"], **report["summary"]}, indent=2))


if __name__ == "__main__":
    main()
