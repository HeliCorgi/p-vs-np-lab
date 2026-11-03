#!/usr/bin/env python3
"""Exact positive control: XOR boundary relations remain affine after projection.

Large examples use exact Gaussian elimination, not full truth-table enumeration.
This experiment concerns the known polynomial-time GF(2) fragment, not general SAT.
Run from the repository root with PYTHONPATH=src.
"""

from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path

from pnp_lab.affine import AffineRelation


def chain_input(n: int) -> tuple[tuple[str, ...], tuple[tuple[tuple[str, ...], int], ...]]:
    if n < 2:
        raise ValueError("Use n >= 2.")
    boundary = tuple(f"x{i}" for i in range(1, n + 1))
    auxiliary = tuple(f"z{i}" for i in range(2, n + 1))
    rows = [(("x1", "x2", "z2"), 0)]
    rows.extend(((f"z{i-1}", f"x{i}", f"z{i}"), 0) for i in range(3, n + 1))
    rows.append(((f"z{n}",), 0))
    return boundary + auxiliary, tuple(rows)


def raw_named_holds(rows, assignment) -> bool:
    return all(sum(assignment[name] for name in terms) % 2 == rhs for terms, rhs in rows)


def verify_size(n: int) -> dict:
    if not 2 <= n <= 1024:
        raise ValueError("Use 2 <= n <= 1024 for this finite matrix experiment.")
    scope, rows = chain_input(n)
    boundary = scope[:n]
    relation = AffineRelation.from_named(scope, rows)
    projected = relation.project(boundary)
    expected = (((1 << n) - 1, 0),)
    if projected.equations != expected:
        raise AssertionError((n, projected.equations, expected))
    boundary_checks = 0
    if n <= 8:
        for bits in product((0, 1), repeat=n):
            named = dict(zip(boundary, bits))
            prefix = bits[0]
            extension = dict(named)
            for index in range(2, n + 1):
                prefix ^= bits[index - 1]
                extension[f"z{index}"] = prefix
            parity_accepts = sum(bits) % 2 == 0
            if projected.holds(named) != parity_accepts or raw_named_holds(rows, extension) != parity_accepts:
                raise AssertionError("Boundary or forced-extension evaluation mismatch.")
            boundary_checks += 1
    full_assignment_checks = 0
    if n <= 5:
        counts = {bits: 0 for bits in product((0, 1), repeat=n)}
        for values in product((0, 1), repeat=2 * n - 1):
            if raw_named_holds(rows, dict(zip(scope, values))):
                counts[values[:n]] += 1
            full_assignment_checks += 1
        if any(count != int(sum(bits) % 2 == 0) for bits, count in counts.items()):
            raise AssertionError("Independent existential enumeration mismatch.")
    return {
        "n": n,
        "input_variables": 2 * n - 1,
        "boundary_variables": n,
        "hidden_variables": n - 1,
        "input_affine_equations": len(rows),
        "input_max_equation_arity": max(len(terms) for terms, _ in rows),
        "normalized_source_equations": len(relation.equations),
        "projected_equations": len(projected.equations),
        "projected_constraint": {"mask": projected.equations[0][0], "rhs": 0, "arity": n},
        "projected_coefficient_row_bits": n,
        "ordinary_boundary_cnf_minimum_clauses": 1 << (n - 1),
        "full_boundary_assignments_checked": boundary_checks,
        "independent_full_assignments_checked": full_assignment_checks,
        "large_n_validation": "Exact finite GF(2) row elimination and coefficient equality; no truth-table enumeration at n > 8.",
        "checks_passed": True,
    }


def run_experiment(sizes=(4, 8, 16, 32, 64, 128, 256)) -> dict:
    selected = sorted(set(sizes))
    if not selected:
        raise ValueError("Choose at least one size.")
    return {
        "schema_version": 1,
        "experiment": "affine_projection",
        "status": "verified",
        "claim_type": "Positive control in the known tractable GF(2) fragment.",
        "semantics": "Rows are linear equations modulo two; join conjoins them on shared variable names; projection existentially removes the hidden variables.",
        "algorithm": "Reduce with hidden columns first, discard hidden-pivot equations, remap surviving constraints to the requested boundary order, then normalize.",
        "representation_contrast": "The same even-parity boundary relation needs 2^(n-1) ordinary CNF clauses without auxiliaries, but one native XOR equation.",
        "generic_semantic_tests": "tests/test_affine.py contains 120 fixed-seed random projection checks and 80 fixed-seed random join checks against independent brute-force semantics, including empty scopes and reordering.",
        "resource_scope": "Dense row elimination has polynomial bit complexity. Python integers encode finite rows; their shifts, XORs, and popcounts are not treated as constant-cost operations on unbounded data. Intermediate rows can become denser than the original width-three equations.",
        "not_claimed": ["A solution of general SAT or P versus NP.", "All relation languages are closed under efficient projection.", "Large-n full truth-table or full auxiliary-assignment enumeration."],
        "sources": [
            {"title": "On SAT representations of XOR constraints", "authors": ["Matthew Gwynne", "Oliver Kullmann"], "url": "https://arxiv.org/abs/1309.3060", "use": "Context for GF(2) systems, XOR representations, and the distinction between native constraints and CNF encodings."},
            {"title": "CNF Encodings of Parity", "url": "https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2022.47", "use": "Known 2^(n-1) ordinary CNF representation lower bound used for comparison."},
        ],
        "cases": [verify_size(n) for n in selected],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=[4, 8, 16, 32, 64, 128, 256])
    args = parser.parse_args()
    payload = run_experiment(args.sizes)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    destination = args.out_dir / "affine_projection.json"
    destination.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "verified", "cases": len(payload["cases"]), "output": str(destination)}, sort_keys=True))


if __name__ == "__main__":
    main()
