#!/usr/bin/env python3
"""Check general width<=3 SAT coverage by constant-size group-local CNF.

A direct source truth-table oracle checks small instances; exact target decisions
come from the existing signature counter. The disjoint-clause family separately
shows exponential growth in that counter's retained global signature states,
although every local group has size two and the source is easy.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

from pnp_lab.block_bridge import three_cnf_to_constant_blocks
from pnp_lab.signatures import count_by_signatures


SEED = 681247


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def values_of(mask: int, n: int) -> tuple[int, ...]:
    return tuple((mask >> i) & 1 for i in range(n))


def raw_cnf_holds(clauses, values) -> bool:
    """Read original signed literals directly, independently of solver helpers."""
    return all(any(values[abs(literal) - 1] == int(literal > 0) for literal in clause)
               for clause in clauses)


def raw_target_holds(reduction, assignment: int) -> bool:
    values = values_of(assignment, len(reduction.bridge.affine.variables))
    return (raw_cnf_holds(reduction.bridge.cnf, values)
            and all(sum(values[i] for i in range(len(values)) if row & (1 << i)) % 2 == rhs
                    for row, rhs in reduction.bridge.affine.equations))


def check_structure(reduction) -> dict:
    names = reduction.bridge.affine.variables
    flattened = tuple(name for group in reduction.groups for name in group)
    require(len(flattened) == len(set(flattened)) == len(names)
            and set(flattened) == set(names), "Groups must partition the target scope.")
    require(all(1 <= len(group) <= 5 for group in reduction.groups), "Group-size bound failed.")
    owner = {name: index for index, group in enumerate(reduction.groups) for name in group}
    for clause in reduction.bridge.cnf:
        if clause:
            require(len(clause) == 2, "Target nonempty clauses must be binary.")
            require(len({owner[names[abs(literal) - 1]] for literal in clause}) == 1,
                    "A target CNF clause crosses groups.")
    seen = 0
    for mask, rhs in reduction.bridge.affine.equations:
        require(mask.bit_count() == 3 and rhs == 0, "Unexpected XOR row shape.")
        require(not (seen & mask), "Native XOR rows must use disjoint helper triples.")
        seen |= mask
    m = len(reduction.original_cnf)
    has_empty = any(not clause for clause in reduction.original_cnf)
    if has_empty:
        require(names == () and reduction.bridge.cnf == ((),) and reduction.groups == (),
                "Empty-clause target must be canonical false on the empty scope.")
    else:
        require(len(reduction.groups) == len(reduction.copy_variables) == 3 * m,
                "Expected three occurrence copies and groups per padded source clause.")
        require(len(reduction.bridge.affine.equations) <= 4 * m and len(names) <= 15 * m,
                "Linear construction bounds failed.")
        require(all(len(clause) == 3 for clause in reduction.expanded_cnf),
                "Every expanded nonempty clause must have exactly three occurrences.")
        frequency = Counter(reduction.copy_to_original)
        require(all(len(group) == (5 if frequency[reduction.copy_to_original[i]] >= 2 else 2)
                    for i, group in enumerate(reduction.groups)),
                "Helpers were not attached to their occurrence-copy groups.")
    return {
        "source_variables": len(reduction.original_variables),
        "source_clauses": m,
        "has_empty_source_clause": has_empty,
        "occurrence_copies": len(reduction.copy_variables),
        "expanded_clauses": len(reduction.expanded_cnf),
        "target_variables": len(names),
        "target_cnf_clauses": len(reduction.bridge.cnf),
        "target_xor_rows": len(reduction.bridge.affine.equations),
        "groups": len(reduction.groups),
        "max_group_size": max((len(group) for group in reduction.groups), default=0),
        "all_target_cnf_group_local": True,
        "native_xor_triples_pairwise_disjoint": True,
    }


def check_local_supports(reduction, result) -> None:
    if any(not clause for clause in reduction.original_cnf):
        return
    signs = [literal > 0 for clause in reduction.original_cnf
             for literal in clause + (clause[-1],) * (3 - len(clause))]
    frequency = Counter(reduction.copy_to_original)
    for copy, original in enumerate(reduction.copy_to_original):
        has_cycle = frequency[original] >= 2
        expected_support = 5 if has_cycle else 2
        expected_valid = (10 if signs[copy] else 8) if has_cycle else 3
        require(result["group_signature_counts"][copy] == expected_support,
                "Unexpected number of distinct local XOR signatures.")
        require(result["group_valid_assignment_counts"][copy] == expected_valid,
                "Unexpected local CNF model count.")


def check_formula(name: str, variables, clauses) -> dict:
    reduction = three_cnf_to_constant_blocks(variables, clauses)
    shape = check_structure(reduction)
    models = {mask for mask in range(1 << len(variables))
              if raw_cnf_holds(clauses, values_of(mask, len(variables)))}
    result = count_by_signatures(reduction.bridge.affine, reduction.bridge.cnf, reduction.groups)
    require(result["exhaustive"] and result["status"] == ("SAT" if models else "UNSAT"),
            "Exact target decision disagrees with the direct source oracle.")
    check_local_supports(reduction, result)
    active_mask = sum(1 << original for original in set(reduction.copy_to_original))
    for original in range(1 << len(variables)):
        if original in models:
            lifted = reduction.lift_witness(original)
            require(raw_target_holds(reduction, lifted), "Lifted witness fails raw target semantics.")
            require(reduction.project_witness(lifted) == original & active_mask,
                    "Witness round trip disagrees on an active source variable.")
        else:
            try:
                reduction.lift_witness(original)
            except ValueError:
                pass
            else:
                raise AssertionError("A source nonmodel was accepted by lift_witness.")
    projected = None
    if models:
        require(raw_target_holds(reduction, result["witness_mask"]),
                "Counter witness fails the direct target checker.")
        projected = reduction.project_witness(result["witness_mask"])
        require(projected in models, "Projected target witness fails the source oracle.")
    return {
        "name": name,
        "original_variables": variables,
        "original_cnf": clauses,
        "shape": shape,
        "source_assignments_checked": 1 << len(variables),
        "source_model_count": len(models),
        "source_models_lifted_and_checked": len(models),
        "target_status": result["status"],
        "target_model_count": result["model_count"],
        "projected_source_witness_mask": projected,
        "group_sizes": result["group_sizes"],
        "group_valid_assignment_counts": result["group_valid_assignment_counts"],
        "group_signature_counts": result["group_signature_counts"],
        "group_assignments_tested": result["group_assignments_tested"],
        "dp_states_peak": result["dp_states_peak"],
        "join_products": result["join_products"],
        "checks_passed": True,
    }


def check_one_clause_target_oracle() -> dict:
    reduction = three_cnf_to_constant_blocks(("a", "b", "c"), ((1, 2, 3),))
    source_models = {mask for mask in range(8) if raw_cnf_holds(((1, 2, 3),), values_of(mask, 3))}
    projected = set()
    count = 0
    for assignment in product((0, 1), repeat=6):
        mask = sum(bit << i for i, bit in enumerate(assignment))
        if raw_target_holds(reduction, mask):
            count += 1
            projected.add(reduction.project_witness(mask))
    require(count == 13 and projected == source_models and len(source_models) == 7,
            "Independent one-clause target oracle failed.")
    return {"source_assignments_checked": 8, "target_assignments_checked": 64,
            "source_model_count": 7, "target_model_count": 13,
            "projected_source_models": sorted(projected), "checks_passed": True}


def check_disjoint_family() -> list[dict]:
    cases = []
    for m in range(1, 13):
        variables = tuple(f"x{i}" for i in range(3 * m))
        clauses = tuple((3 * i + 1, 3 * i + 2, 3 * i + 3) for i in range(m))
        reduction = three_cnf_to_constant_blocks(variables, clauses)
        shape = check_structure(reduction)
        result = count_by_signatures(reduction.bridge.affine, reduction.bridge.cnf, reduction.groups)
        check_local_supports(reduction, result)
        require(result["status"] == "SAT" and result["exhaustive"], "Family count is incomplete.")
        require(result["group_sizes"] == [2] * (3 * m), "Expected only two-variable groups.")
        require(result["model_count"] == 13 ** m, "Family target count formula failed.")
        require(result["group_assignments_tested"] == 12 * m, "Family local-work formula failed.")
        require(result["dp_states_peak"] == result["dp_state_counts"][-1] == 2 ** m,
                "Family retained-state formula failed.")
        require(result["join_products"] == 10 * (2 ** m - 1), "Family join-work formula failed.")
        projected = reduction.project_witness(result["witness_mask"])
        require(raw_target_holds(reduction, result["witness_mask"])
                and raw_cnf_holds(clauses, values_of(projected, len(variables))),
                "Family witness check failed.")
        cases.append({
            "m": m, "shape": shape,
            "source_model_count_by_independent_clause_product": 7 ** m,
            "target_model_count": result["model_count"],
            "max_group_signature_count": max(result["group_signature_counts"]),
            "group_assignments_tested": result["group_assignments_tested"],
            "dp_states_peak": result["dp_states_peak"],
            "dp_state_counts": result["dp_state_counts"],
            "join_products": result["join_products"],
            "join_products_by_group": result["join_products_by_group"],
            "projected_source_witness_mask": projected,
            "checks_passed": True,
        })
    return cases


def run_experiment() -> dict:
    rng = random.Random(SEED)
    random_cases = []
    for index in range(40):
        n = rng.randint(1, 4)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(1, 3)))
                        for _ in range(rng.randint(0, 2)))
        random_cases.append(check_formula(f"seeded_{index:02}", tuple(f"x{i}" for i in range(n)), clauses))
    controls = [
        check_formula("empty_scope_true", (), ()),
        check_formula("unused_scope_true", ("unused",), ()),
        check_formula("empty_scope_false", (), ((),)),
        check_formula("empty_clause_with_scope", ("x", "unused"), ((1,), ())),
        check_formula("positive_unit", ("x",), ((1,),)),
        check_formula("negative_unit", ("x",), ((-1,),)),
        check_formula("opposed_units", ("x",), ((1,), (-1,))),
        check_formula("signed_binary", ("x", "y", "unused"), ((1, -2),)),
        check_formula("repeated_literal", ("x", "y"), ((1, 1, -2),)),
        check_formula("tautological_source", ("x", "y"), ((1, -1, 2),)),
    ]
    direct = check_one_clause_target_oracle()
    family = check_disjoint_family()
    small_cases = random_cases + controls
    return {
        "schema_version": 1,
        "experiment": "constant_block_bridge",
        "constructor": "pnp_lab.block_bridge.three_cnf_to_constant_blocks",
        "status": "verified",
        "random_seed": SEED,
        "construction": "Pad each nonempty source clause to three literal occurrences; give each occurrence a fresh copy; for t>=2 copies of a variable add t padded implication-cycle clauses (-copy_i,copy_next,copy_next); apply the existing 3-CNF bridge; group each copy with all its helpers.",
        "bounds_for_m_nonempty_source_clauses": {"groups": "3m", "maximum_group_size": 5,
                                                 "target_xor_rows_at_most": "4m", "target_variables_at_most": "15m"},
        "preservation": "Satisfiability with constructive lift/project maps. Counts are not preserved. Unused source variables are metadata only and project to False.",
        "empty_clause_policy": "After complete input validation, any empty source clause gives an empty-scope target with one empty CNF clause and no groups.",
        "local_support_identity": "A copy in an equality cycle has exactly five local signatures and ten local CNF models for a positive source occurrence or eight for a negative occurrence. A singleton copy has two signatures and three local models.",
        "random_oracle_cases": random_cases,
        "control_cases": controls,
        "independent_one_clause_target_oracle": direct,
        "disjoint_positive_triples": family,
        "disjoint_family_formulas": {"source_models": "7^m", "target_models": "13^m",
                                     "group_size": 2, "local_assignment_visits": "12m",
                                     "retained_dp_states": "2^m", "join_products": "10(2^m-1)"},
        "interpretation": "The disjoint-clause family is easy. Its exponential state growth is specific to the current counter, which retains completed XOR rows. Retiring completed rows or factoring disconnected components can remove this example's blowup. This is not an intrinsic SAT lower bound, and constant local tables alone do not bound global joining work.",
        "summary": {
            "random_oracle_cases": len(random_cases), "control_cases": len(controls),
            "small_oracle_sat_cases": sum(case["target_status"] == "SAT" for case in small_cases),
            "small_oracle_unsat_cases": sum(case["target_status"] == "UNSAT" for case in small_cases),
            "source_assignments_checked": sum(case["source_assignments_checked"] for case in small_cases),
            "source_models_lifted_and_checked": sum(case["source_models_lifted_and_checked"] for case in small_cases),
            "direct_target_assignments_checked": direct["target_assignments_checked"],
            "disjoint_family_cases": len(family),
            "max_group_size": max(case["shape"]["max_group_size"] for case in small_cases),
            "max_local_signature_count": max((count for case in small_cases
                                               for count in case["group_signature_counts"]), default=0),
            "largest_disjoint_m": family[-1]["m"],
            "largest_disjoint_dp_states": family[-1]["dp_states_peak"],
            "largest_disjoint_join_products": family[-1]["join_products"],
            "largest_disjoint_local_assignment_visits": family[-1]["group_assignments_tested"],
        },
        "all_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    payload = run_experiment()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    destination = args.out_dir / "constant_block_bridge.json"
    destination.write_text(json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "verified", "output": str(destination),
                      "all_checks_passed": True, **payload["summary"]}, sort_keys=True))


if __name__ == "__main__":
    main()
