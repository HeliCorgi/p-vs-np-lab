#!/usr/bin/env python3
"""Exact group-signature counting, useful families, and an explicit-table barrier.

The report counts executed assignments and products, not wall-clock time.
It implements a finite GF(2) specialization of conditioning on measurements,
not the openai/math subexponential SAT algorithm.
"""

from __future__ import annotations

import argparse
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from pnp_lab.affine import AffineRelation
from pnp_lab.signatures import count_by_signatures


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def names(n):
    return tuple(f"x{i + 1}" for i in range(n))


def exactly_one(literals):
    literals = tuple(literals)
    return (literals,) + tuple((-a, -b) for a, b in combinations(literals, 2))


def block_formula(blocks):
    scope = names(3 * blocks)
    groups = tuple(scope[3 * i:3 * i + 3] for i in range(blocks))
    cnf = tuple(clause for i in range(blocks)
                for clause in exactly_one(range(3 * i + 1, 3 * i + 4)))
    return scope, groups, cnf


def raw_holds(n, rows, cnf, assignment):
    if type(assignment) is not int or not 0 <= assignment < 1 << n:
        return False
    bits = tuple((assignment >> i) & 1 for i in range(n))
    return (all(sum(bits[i] for i in range(n) if (mask >> i) & 1) % 2 == rhs
                for mask, rhs in rows)
            and all(any(bits[abs(lit) - 1] == (lit > 0) for lit in clause) for clause in cnf))


def raw_models(n, rows, cnf):
    return [assignment for assignment in range(1 << n) if raw_holds(n, rows, cnf, assignment)]


def checked_result(scope, rows, cnf, groups, expected_count):
    result = count_by_signatures(AffineRelation(scope, rows), cnf, groups)
    require(result["model_count"] == expected_count, "exact count disagrees with expected count")
    require(result["status"] == ("SAT" if expected_count else "UNSAT"), "incorrect exact status")
    require(result["exhaustive"], "unbudgeted run should finish")
    if expected_count:
        require(raw_holds(len(scope), rows, cnf, result["witness_mask"]),
                "returned witness violates original raw input")
        require(result["witness"] == {name: (result["witness_mask"] >> i) & 1
                                      for i, name in enumerate(scope)}, "witness naming changed")
    else:
        require(result["witness_mask"] is None and result["witness"] is None, "UNSAT has a witness")
    return result


def short_result(result):
    keys = ("status", "reason", "exhaustive", "model_count", "n_variables", "n_groups",
            "signature_bits", "target_signature", "max_block_size",
            "group_assignments_tested", "group_assignments_tested_by_group",
            "group_valid_assignment_counts", "group_signature_counts", "group_tables_complete",
            "dp_state_counts", "dp_states_peak", "join_products", "join_products_by_group",
            "join_groups_completed", "join_partial_group_index", "join_partial_state_count")
    return {key: result[key] for key in keys}


def run():
    coupled = []
    for blocks in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        scope, groups, cnf = block_formula(blocks)
        n = len(scope)
        expected = 3 ** blocks
        sat_rows = (((1 << n) - 1, blocks % 2),)
        unsat_rows = (((1 << n) - 1, 1 ^ (blocks % 2)),)
        sat = checked_result(scope, sat_rows, cnf, groups, expected)
        unsat = checked_result(scope, unsat_rows, cnf, groups, 0)
        for result in (sat, unsat):
            require(result["group_assignments_tested"] == 8 * blocks, "triple visit count")
            require(result["group_signature_counts"] == [1] * blocks, "one signature per triple")
            require(result["dp_state_counts"] == [1] * (blocks + 1), "one accumulated signature")
            require(result["join_products"] == blocks, "one product per triple join")
        oracle_checked = n <= 8
        if oracle_checked:
            require(len(raw_models(n, sat_rows, cnf)) == expected, "small block raw SAT oracle")
            require(not raw_models(n, unsat_rows, cnf), "small block raw UNSAT oracle")
        coupled.append({"blocks": blocks, "n": n, "expected_models_decimal": str(expected),
                        "raw_oracle_checked": oracle_checked,
                        "sat": short_result(sat), "opposite_parity_unsat": short_result(unsat),
                        "checks_passed": True})

    two_bit = []
    for blocks in (1, 2, 3, 4, 8, 16, 32, 64):
        scope, groups, cnf = block_formula(blocks)
        first = sum(1 << (3 * i) for i in range(blocks))
        second = sum(1 << (3 * i + 1) for i in range(blocks))
        for right_first, right_second in product((0, 1), repeat=2):
            numerator = (3 ** blocks + (-1) ** right_first + (-1) ** right_second
                         + (-1) ** (right_first + right_second + blocks))
            require(numerator % 4 == 0, "two-bit count formula must be integral")
            expected = numerator // 4
            rows = ((first, right_first), (second, right_second))
            result = checked_result(scope, rows, cnf, groups, expected)
            require(result["signature_bits"] == 2, "two independent boundary measurements")
            require(result["group_signature_counts"] == [3] * blocks, "three local signatures")
            require(result["dp_state_counts"] == [1, 3] + [4] * (blocks - 1), "two-bit DP support")
            require(result["join_products"] == (3 if blocks == 1 else 12 * blocks - 12),
                    "two-bit convolution product count")
            oracle_checked = len(scope) <= 8
            if oracle_checked:
                require(len(raw_models(len(scope), rows, cnf)) == expected, "two-bit raw oracle")
            two_bit.append({"blocks": blocks, "rhs": [right_first, right_second],
                            "expected_models_decimal": str(expected),
                            "raw_oracle_checked": oracle_checked, "solver": short_result(result),
                            "checks_passed": True})

    identity = []
    for width in range(1, 15):
        scope = names(width)
        rows = tuple((1 << i, 0) for i in range(width))
        result = checked_result(scope, rows, (), (scope,), 1)
        require(result["group_assignments_tested"] == 1 << width, "identity assignment count")
        require(result["group_signature_counts"] == [1 << width], "identity image size")
        require(result["dp_state_counts"] == [1, 1 << width], "identity joined state count")
        require(result["join_products"] == 1 << width, "identity join work")
        require(result["witness_mask"] == 0, "the unique solution is all zero")
        if width <= 8:
            require(raw_models(width, rows, ()) == [0], "identity raw oracle")
        identity.append({"width": width, "table_entries_predicted": 1 << width,
                         "raw_oracle_checked": width <= 8, "solver": short_result(result),
                         "checks_passed": True})

    rng = random.Random(2026110308)
    oracle = []
    assignments_checked = 0
    for trial in range(144):
        n = trial % 9
        scope = names(n)
        remaining = list(range(n))
        rng.shuffle(remaining)
        groups = []
        while remaining:
            width = rng.randrange(1, min(4, len(remaining)) + 1)
            groups.append(tuple(scope[j] for j in remaining[:width]))
            del remaining[:width]
        planted = rng.randrange(1 << n)
        rows = tuple((mask, ((mask & planted).bit_count() & 1) if trial % 2 else rng.randrange(2))
                     for mask in (rng.randrange(1 << n) for _ in range(rng.randrange(5))))
        clauses = []
        for group in groups:
            local_variables = [scope.index(name) + 1 for name in group]
            for _ in range(rng.randrange(4)):
                clause = [rng.choice((-1, 1)) * rng.choice(local_variables)
                          for _ in range(rng.randrange(1, 5))]
                if trial % 2 and not any(((planted >> (abs(lit) - 1)) & 1) == (lit > 0)
                                         for lit in clause):
                    clause[0] = abs(clause[0]) * (1 if (planted >> (abs(clause[0]) - 1)) & 1 else -1)
                clauses.append(tuple(clause))
        if n:
            clauses.append((1, -1, n))
        if trial % 23 == 0:
            clauses.append(())
        if clauses and trial % 4 == 0:
            clauses.append(clauses[0])
        cnf = tuple(clauses)
        models = raw_models(n, rows, cnf)
        assignments_checked += 1 << n
        result = checked_result(scope, rows, cnf, groups, len(models))
        oracle.append({"case": trial, "n": n, "groups": [list(group) for group in groups],
                       "input_sha256": digest([scope, rows, cnf, groups]),
                       "models": len(models), "solver": short_result(result), "checks_passed": True})

    budget_cases = []
    scope = names(4)
    affine = AffineRelation(scope, tuple((1 << i, 0) for i in range(4)))
    for kwargs in ({"max_group_assignments": 0}, {"max_group_assignments": 15},
                   {"max_join_products": 0}, {"max_join_products": 15},
                   {"max_group_assignments": 16, "max_join_products": 16}):
        result = count_by_signatures(affine, (), (scope,), **kwargs)
        finished = kwargs == {"max_group_assignments": 16, "max_join_products": 16}
        require(result["status"] == ("SAT" if finished else "UNKNOWN"), "budget status")
        require(result["model_count"] == (1 if finished else None), "budget count")
        if not finished:
            require(result["witness"] is None and not result["exhaustive"], "partial output is exact")
        budget_cases.append({"budgets": kwargs, "solver": short_result(result), "checks_passed": True})

    rejected = False
    try:
        count_by_signatures(AffineRelation.truth(("a", "b")), ((1, 2),), (("a",), ("b",)))
    except ValueError as error:
        rejected = "cross-group" in str(error)
    require(rejected, "unsupported cross-group clause was not rejected")

    return {
        "schema_version": 1, "all_checks_passed": True,
        "scope": "Exact finite GF(2) group-signature counting; not a P versus NP resolution.",
        "algorithm_general_polynomial_time": False,
        "counting_note": "Counts are executed local assignment visits and table-pair products; "
                         "integer bit costs and validation are additional. No wall-clock claims.",
        "attribution": {
            "repository": "https://github.com/openai/math",
            "commit": "4eaee87548250b2682affda7d05d947c05554bae",
            "family": 378,
            "component": "Finite measurement/fiber sum-product identity, specialized here to GF(2).",
            "implements_upstream_subexponential_algorithm": False,
        },
        "coupled_exactly_one_blocks": coupled,
        "two_bit_signature_cases": two_bit,
        "identity_measurement_barrier": {
            "claim_scope": "For this explicit table algorithm only, the b-bit identity map "
                           "creates 2^b entries for every b; the all-zero target is easy globally.",
            "all_b_proof": "The signature of u is I_b u = u, so all 2^b local assignments "
                           "have different signatures and each table entry has multiplicity one.",
            "general_sat_lower_bound": False, "cases": identity,
        },
        "independent_oracle": {"seed": 2026110308, "case_count": len(oracle),
                               "original_assignments_checked": assignments_checked, "cases": oracle},
        "budget_cases": budget_cases,
        "cross_group_clause_rejected": rejected,
        "summary": {
            "largest_exactly_one_blocks": coupled[-1]["blocks"],
            "largest_exactly_one_variables": coupled[-1]["n"],
            "largest_exactly_one_models_decimal": coupled[-1]["expected_models_decimal"],
            "largest_exactly_one_group_assignments": coupled[-1]["sat"]["group_assignments_tested"],
            "largest_exactly_one_join_products": coupled[-1]["sat"]["join_products"],
            "largest_two_bit_groups": max(case["blocks"] for case in two_bit),
            "largest_two_bit_dp_states": max(case["solver"]["dp_states_peak"] for case in two_bit),
            "identity_widths_measured": len(identity),
            "largest_identity_signature_table": identity[-1]["solver"]["group_signature_counts"][0],
            "oracle_cases": len(oracle), "oracle_original_assignments_checked": assignments_checked,
            "oracle_sat": sum(case["models"] > 0 for case in oracle),
            "oracle_unsat": sum(case["models"] == 0 for case in oracle),
            "budget_cases_checked": len(budget_cases),
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    report = run()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    path = args.out_dir / "signature_counting.json"
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": report["all_checks_passed"], **report["summary"]}, indent=2))


if __name__ == "__main__":
    main()
