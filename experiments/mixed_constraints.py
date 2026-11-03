#!/usr/bin/env python3
"""Exact experiments for the affine-quotient XOR + CNF enumerator.

The large cases record deterministic counts, not timing-based hardness claims.
The small oracle evaluates the original equations and clauses on every bit tuple;
it does not reuse Gaussian elimination, quotient maps, or solver evaluators.
Run from the repository root with PYTHONPATH=src.
"""

from __future__ import annotations

import argparse
from itertools import combinations, product
import json
from pathlib import Path
import random

from pnp_lab.affine import AffineRelation
from pnp_lab.mixed import (
    check_sat_witness,
    check_unsat_certificate,
    solve_mixed,
)


DEFAULT_SEED = 20261103
DEFAULT_LOW_RANK_SIZES = (64, 128, 256)
DEFAULT_BARRIER_SIZES = (4, 6, 8, 10, 12, 14, 16)
SUMMARY_FIELDS = (
    "status", "n_variables", "affine_consistent", "affine_dimension",
    "effective_rank", "quotient_cells", "checked_cells", "requested_exhaustive", "exhaustive",
    "satisfying_cells", "rejecting_cells", "model_count",
)


def make_affine(n: int, rows: tuple[tuple[int, int], ...]) -> AffineRelation:
    return AffineRelation(tuple(f"x{i}" for i in range(1, n + 1)), rows)


def raw_holds(rows, cnf, values: tuple[int, ...]) -> bool:
    """Read raw syntax on a bit tuple, independently of the solver's evaluators."""
    xor_ok = all(
        sum(value for index, value in enumerate(values) if mask & (1 << index)) % 2 == rhs
        for mask, rhs in rows
    )
    cnf_ok = all(
        any(values[abs(literal) - 1] == int(literal > 0) for literal in clause)
        for clause in cnf
    )
    return xor_ok and cnf_ok


def brute_force(n: int, rows, cnf) -> dict:
    """Count original models, with an explicit small-instance safety bound."""
    if not 0 <= n <= 10:
        raise ValueError("Independent full enumeration is limited to 0 <= n <= 10.")
    count = 0
    first_mask = None
    for values in product((0, 1), repeat=n):
        if raw_holds(rows, cnf, values):
            count += 1
            if first_mask is None:
                first_mask = sum(value << index for index, value in enumerate(values))
    return {
        "assignments_checked": 1 << n,
        "model_count": count,
        "first_model_mask": first_mask,
    }


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def _summary(result: dict) -> dict:
    # Never serialize the full trace or an exponential certificate by accident.
    return {field: result[field] for field in SUMMARY_FIELDS}


def _check_witness(n: int, rows, cnf, affine: AffineRelation, result: dict) -> None:
    mask = result["witness_mask"]
    _require(type(mask) is int and 0 <= mask < (1 << n), "Invalid SAT witness mask.")
    values = tuple((mask >> index) & 1 for index in range(n))
    _require(raw_holds(rows, cnf, values), "Witness fails independent raw evaluation.")
    _require(check_sat_witness(affine, cnf, mask), "Solver witness checker rejected the witness.")


def exactly_one_clauses(variables: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    """One at-least-one clause and every pairwise at-most-one clause."""
    return (variables,) + tuple((-left, -right) for left, right in combinations(variables, 2))


def exactly_one_even_input(k: int) -> tuple[tuple[tuple[int, int], ...], tuple[tuple[int, ...], ...]]:
    if not 3 <= k <= 16:
        raise ValueError("Use 3 <= k <= 16 for this enumerated family.")
    return (((1 << k) - 1, 0),), exactly_one_clauses(tuple(range(1, k + 1)))


def low_rank_input(n: int) -> tuple[tuple[tuple[int, int], ...], tuple[tuple[int, ...], ...]]:
    """Many independent unused bits and many observed copies of three bits.

    There are g=floor(n/6) triples of copies, constrained to equal x1,x2,x3.
    Exactly-one is imposed on the base triple and on every copy triple.
    The remaining n-3-3g coordinates are independent and absent from the CNF.
    """
    if not 6 <= n <= 1024:
        raise ValueError("Use 6 <= n <= 1024 for the low-rank family.")
    groups = n // 6
    rows = []
    cnf = list(exactly_one_clauses((1, 2, 3)))
    for group in range(groups):
        copied_variables = tuple(4 + 3 * group + offset for offset in range(3))
        rows.extend(((1 << offset) | (1 << (variable - 1)), 0)
                    for offset, variable in enumerate(copied_variables))
        cnf.extend(exactly_one_clauses(copied_variables))
    return tuple(rows), tuple(cnf)


def verify_low_rank(n: int) -> dict:
    rows, cnf = low_rank_input(n)
    affine = make_affine(n, rows)
    result = solve_mixed(affine, cnf, exhaustive=True,
                         include_trace=False, include_certificate=False)
    groups = n // 6
    dimension = n - 3 * groups
    expected_models = 3 * (1 << (dimension - 3))
    _require(result["status"] == "SAT", "Low-rank family must be satisfiable.")
    _require(result["affine_dimension"] == dimension, "Low-rank affine dimension mismatch.")
    _require(result["effective_rank"] == 3, "Observed forms must have rank three.")
    _require(result["quotient_cells"] == result["checked_cells"] == 8,
             "Exhaustive low-rank search must check exactly eight quotient cells.")
    _require(result["exhaustive"] and result["satisfying_cells"] == 3
             and result["rejecting_cells"] == 5, "Low-rank quotient counts mismatch.")
    _require(result["model_count"] == expected_models, "Fiber multiplicity was not counted correctly.")
    _check_witness(n, rows, cnf, affine, result)
    oracle = brute_force(n, rows, cnf) if n <= 10 else None
    if oracle is not None:
        _require(oracle["model_count"] == expected_models, "Raw low-rank oracle mismatch.")
    return {
        "family": "many_free_bits_few_observed_forms",
        "n": n,
        "copy_triples": groups,
        "raw_xor_equations": len(rows),
        "raw_cnf_clauses": len(cnf),
        "raw_cnf_literal_occurrences": sum(map(len, cnf)),
        "cnf_occurring_variables": 3 + 3 * groups,
        "unobserved_free_bits": dimension - 3,
        "full_affine_assignments": 1 << dimension,
        "predicted_model_count": expected_models,
        "exhaustive_requested": True,
        "solver": _summary(result),
        "witness_mask": result["witness_mask"],
        "witness_checked_in_raw_input": True,
        "independent_oracle": oracle,
        "validation": "Exact quotient enumeration plus the copy-equation and exactly-one counting argument; full original enumeration only when n <= 10.",
        "checks_passed": True,
    }


def verify_enumeration_barrier(k: int) -> dict:
    rows, cnf = exactly_one_even_input(k)
    affine = make_affine(k, rows)
    small_certificate = k <= 6
    # Decision mode may return immediately on a model. Here there is no model,
    # so the exponential count is not caused by requesting model counting.
    result = solve_mixed(affine, cnf, exhaustive=False, include_trace=False,
                         include_certificate=small_certificate)
    expected_cells = 1 << (k - 1)
    _require(affine.is_consistent, "Even-parity equation is consistent.")
    _require(all(len(clause) >= 2 for clause in cnf), "Family must have no empty or unit clauses.")
    _require(result["status"] == "UNSAT" and result["model_count"] == 0,
             "Exactly-one and even parity must be incompatible.")
    _require(result["requested_exhaustive"] is False,
             "The barrier experiment must use the early-stopping decision mode.")
    _require(result["affine_dimension"] == result["effective_rank"] == k - 1,
             "All coordinate forms span the even-parity space's dual.")
    _require(result["quotient_cells"] == result["checked_cells"] == expected_cells,
             "This enumerator must visit all quotient cells in this UNSAT family.")
    _require(result["exhaustive"] and result["satisfying_cells"] == 0
             and result["rejecting_cells"] == expected_cells, "Barrier quotient counts mismatch.")
    certificate_verified = None
    if small_certificate:
        certificate_verified = check_unsat_certificate(affine, cnf, result["certificate"])
        _require(certificate_verified, "Small full UNSAT certificate was rejected.")
    oracle = brute_force(k, rows, cnf) if k <= 8 else None
    if oracle is not None:
        _require(oracle["model_count"] == 0, "Independent original-assignment oracle found a model.")
    return {
        "family": "exactly_one_with_even_parity",
        "k": k,
        "raw_xor_equations": 1,
        "raw_cnf_clauses": 1 + k * (k - 1) // 2,
        "raw_cnf_literal_occurrences": k * k,
        "has_empty_or_unit_clause": False,
        "predicted_checked_cells": expected_cells,
        "exhaustive_requested": False,
        "search_mode": "decision; stop at the first model if one is found",
        "solver": _summary(result),
        "full_certificate_checked": certificate_verified,
        "full_certificate_serialized": False,
        "independent_oracle": oracle,
        "claim_scope": "Exact candidate count for this quotient enumerator. The family has an elementary contradiction and is not a lower bound for all SAT algorithms.",
        "checks_passed": True,
    }


def _curated_cases() -> tuple:
    return (
        ("empty_true", 0, (), ()),
        ("empty_clause_on_empty_scope", 0, (), ((),)),
        ("affine_contradiction", 1, ((0, 1),), ()),
        ("fixed_variables_sat", 2, ((1, 1), (2, 0)), ((1, -2),)),
        ("fixed_variables_unsat", 2, ((1, 1), (2, 0)), ((-1, 2),)),
        ("duplicate_and_tautological_clauses", 3, ((3, 0), (3, 0)),
         ((1, -1), (2, 2, 3), (2, 2, 3))),
        ("unused_free_variables", 4, ((3, 1),), ((1, 2),)),
        ("empty_clause_with_other_constraints", 3, ((5, 1),), ((1, 2), ())),
    )


def random_inputs(count: int, seed: int = DEFAULT_SEED) -> tuple:
    """Deterministic raw cases with planted and unplanted satisfiability modes."""
    if not 1 <= count <= 200:
        raise ValueError("Choose 1 <= random case count <= 200.")
    rng = random.Random(seed)
    cases = []
    for index in range(count):
        n = rng.randrange(1, 8)
        planted = tuple(rng.randrange(2) for _ in range(n))
        mode = index % 3
        rows = []
        for _ in range(rng.randrange(n + 3)):
            mask = rng.randrange(1 << n)
            rhs = rng.randrange(2) if mode == 0 else sum(
                value for bit, value in enumerate(planted) if mask & (1 << bit)
            ) % 2
            rows.append((mask, rhs))
        cnf = []
        for _ in range(rng.randrange(9)):
            length = rng.randrange(1, 5)
            clause = [rng.choice((-1, 1)) * rng.randrange(1, n + 1) for _ in range(length)]
            if mode == 1:
                variable = abs(clause[0])
                clause[0] = variable if planted[variable - 1] else -variable
            cnf.append(tuple(clause))
        if index % 7 == 0:
            variable = rng.randrange(1, n + 1)
            cnf.append((variable, -variable))
        if index % 11 == 0:
            if rows:
                rows.append(rows[0])
            if cnf:
                cnf.append(cnf[0])
        if mode != 1 and index % 29 == 0:
            cnf.append(())
        cases.append((f"random_{index:03d}", n, tuple(rows), tuple(cnf)))
    return tuple(cases)


def verify_random_oracle(random_cases: int = 128, seed: int = DEFAULT_SEED) -> dict:
    records = []
    for name, n, rows, cnf in _curated_cases() + random_inputs(random_cases, seed):
        oracle = brute_force(n, rows, cnf)
        affine = make_affine(n, rows)
        result = solve_mixed(affine, cnf, exhaustive=True,
                             include_trace=False, include_certificate=True)
        expected_status = "SAT" if oracle["model_count"] else "UNSAT"
        _require(result["status"] == expected_status, f"{name}: raw SAT/UNSAT mismatch.")
        _require(result["exhaustive"], f"{name}: an unbounded exhaustive run did not finish.")
        _require(result["model_count"] == oracle["model_count"], f"{name}: raw model-count mismatch.")
        certificate_verified = None
        if expected_status == "SAT":
            _check_witness(n, rows, cnf, affine, result)
        else:
            certificate_verified = check_unsat_certificate(affine, cnf, result["certificate"])
            _require(certificate_verified, f"{name}: UNSAT certificate was rejected.")
        records.append({
            "name": name,
            "n": n,
            "raw_xor_rows": rows,
            "raw_cnf": cnf,
            "oracle": oracle,
            "solver": _summary(result),
            "witness_mask": result["witness_mask"],
            "full_certificate_checked": certificate_verified,
            "checks_passed": True,
        })
    def coverage(cases: list[dict]) -> dict:
        consistent = [case for case in cases if case["solver"]["affine_consistent"]]
        return {
            "cases": len(cases),
            "affine_consistent": len(consistent),
            "affine_inconsistent": len(cases) - len(consistent),
            "sat": sum(case["solver"]["status"] == "SAT" for case in cases),
            "unsat": sum(case["solver"]["status"] == "UNSAT" for case in cases),
            "consistent_xor_but_mixed_unsat": sum(case["solver"]["status"] == "UNSAT" for case in consistent),
            "rank_less_than_dimension": sum(case["solver"]["effective_rank"] < case["solver"]["affine_dimension"] for case in consistent),
            "rank_equal_dimension": sum(case["solver"]["effective_rank"] == case["solver"]["affine_dimension"] for case in consistent),
            "positive_observation_rank": sum(case["solver"]["effective_rank"] > 0 for case in consistent),
            "positive_rank_less_than_dimension": sum(0 < case["solver"]["effective_rank"] < case["solver"]["affine_dimension"] for case in consistent),
            "positive_rank_equal_dimension": sum(0 < case["solver"]["effective_rank"] == case["solver"]["affine_dimension"] for case in consistent),
        }
    random_records = records[len(_curated_cases()):]
    return {
        "seed": seed,
        "random_cases": random_cases,
        "curated_cases": len(_curated_cases()),
        "max_variables": max(case["n"] for case in records),
        "full_original_assignments_checked": sum(case["oracle"]["assignments_checked"] for case in records),
        "sat_cases": sum(case["solver"]["status"] == "SAT" for case in records),
        "unsat_cases": sum(case["solver"]["status"] == "UNSAT" for case in records),
        "random_planted_consistent_xor_cases": sum(index % 3 != 0 for index in range(random_cases)),
        "random_generation": "Two of every three cases derive XOR right-hand sides from a planted assignment; one of those also plants satisfied CNF clauses. The remaining cases use arbitrary right-hand sides.",
        "random_coverage": coverage(random_records),
        "all_case_coverage": coverage(records),
        "cases": records,
        "checks_passed": True,
    }


def verify_budget_control() -> dict:
    """A truncated search cannot turn absence of a found model into UNSAT."""
    k, budget = 6, 3
    rows, cnf = exactly_one_even_input(k)
    result = solve_mixed(make_affine(k, rows), cnf, exhaustive=False, max_cells=budget,
                         include_trace=False, include_certificate=True)
    _require(result["status"] == "UNKNOWN", "A partial rejecting trace cannot prove UNSAT.")
    _require(result["checked_cells"] == budget < result["quotient_cells"],
             "Budget control did not stop before full coverage.")
    _require(not result["exhaustive"] and result["model_count"] is None,
             "Incomplete search cannot publish an exact model count.")
    _require(result["certificate"] is None, "Incomplete search cannot publish a full UNSAT certificate.")
    return {"family": "budget_must_preserve_unknown", "max_cells": budget,
            "exhaustive_requested": False,
            "solver": _summary(result), "checks_passed": True}


def run_experiment(low_rank_sizes=DEFAULT_LOW_RANK_SIZES,
                   barrier_sizes=DEFAULT_BARRIER_SIZES,
                   random_cases: int = 128, seed: int = DEFAULT_SEED) -> dict:
    low_sizes = sorted(set(low_rank_sizes))
    hard_sizes = sorted(set(barrier_sizes))
    if not low_sizes or not hard_sizes:
        raise ValueError("Choose at least one size for each structural family.")
    return {
        "schema_version": 1,
        "experiment": "mixed_constraints",
        "status": "verified",
        "claim_type": "Exact affine-quotient enumeration with a small observed-rank regime and a proved superpolynomial family for this algorithm.",
        "algorithm": "Write x=c+B t; span the coefficient forms of variables occurring in normalized CNF; enumerate all 2^r quotient values and lift one representative per equal-CNF fiber.",
        "rank_scope": "r is the rank of syntactically observed coordinate forms after original-CNF tautology and duplicate removal. It is not a minimum residual nonlinear dimension.",
        "resource_scope": "Preprocessing and representative evaluation have polynomial bit cost; enumeration contributes 2^r. All variables are explicitly scoped. Unbounded integers and exponentially many certificate cells are not assigned unit cost.",
        "low_rank_cases": [verify_low_rank(n) for n in low_sizes],
        "enumeration_barrier_cases": [verify_enumeration_barrier(k) for k in hard_sizes],
        "independent_oracle": verify_random_oracle(random_cases, seed),
        "budget_control": verify_budget_control(),
        "not_claimed": [
            "A polynomial-time algorithm for arbitrary SAT or a resolution of P versus NP.",
            "A lower bound for all algorithms, all preprocessing, or all constraint representations.",
            "That the exactly-one/even-parity family is intrinsically difficult; its contradiction is immediate from its structure.",
            "A polynomial-size UNSAT certificate or polynomial-time certificate check at unrestricted rank.",
            "Full original-variable enumeration in the large low-rank cases.",
        ],
        "all_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--low-rank-sizes", nargs="+", type=int, default=DEFAULT_LOW_RANK_SIZES)
    parser.add_argument("--barrier-sizes", nargs="+", type=int, default=DEFAULT_BARRIER_SIZES)
    parser.add_argument("--random-cases", type=int, default=128)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    args = parser.parse_args()
    payload = run_experiment(args.low_rank_sizes, args.barrier_sizes, args.random_cases, args.seed)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    destination = args.out_dir / "mixed_constraints.json"
    destination.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
                           encoding="utf-8")
    print(json.dumps({
        "status": "verified",
        "low_rank_cases": len(payload["low_rank_cases"]),
        "enumeration_barrier_cases": len(payload["enumeration_barrier_cases"]),
        "oracle_cases": len(payload["independent_oracle"]["cases"]),
        "output": str(destination),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
