#!/usr/bin/env python3
"""Reproduce the two-/three-option XOR support threshold controls."""

from __future__ import annotations

import argparse
from functools import reduce
from itertools import product
import json
from operator import xor
from pathlib import Path
import random

from pnp_lab.frontier import decide_signature_supports
from pnp_lab.ternary_support import (decide_ternary_reduction, three_cnf_to_ternary_supports,
                                     three_cnf_to_weight_two_supports)


SEED = 3081062


def require(value, message):
    if not value:
        raise AssertionError(message)


def raw_models(n, cnf):
    return {sum(b << i for i, b in enumerate(bits)) for bits in product((0, 1), repeat=n)
            if all(any(bits[abs(lit)-1] == int(lit > 0) for lit in clause) for clause in cnf)}


def binary_cases():
    rows = []
    for d in (4, 16, 64, 256):
        # Cycle-edge difference vectors span the even-weight subspace.
        # Anchors translate that space, so flipping one target bit swaps feasibility.
        groups = []
        for j in range(d):
            anchor = (1 << j) | (1 << ((7*j+3) % d))
            difference = (1 << j) ^ (1 << ((j+1) % d))
            groups.append((anchor, anchor ^ difference))
        rhs = reduce(xor, (s[(j % 3) != 0] for j, s in enumerate(groups)), 0)
        sat = decide_signature_supports(groups, rhs, max_transitions=0)
        neg = decide_signature_supports(groups, rhs ^ 1, max_transitions=0)
        require(sat["status"] == "SAT" and neg["status"] == "UNSAT", "Binary coset oracle")
        require(all(r["affine_rank"] == d-1 and r["affine_groups"] == d
                    and r["transitions"] == 0 for r in (sat, neg)), "Binary elimination")
        require(reduce(xor, sat["witness"], 0) == rhs and
                all(x in s for x, s in zip(sat["witness"], groups)), "Binary witness")
        rows.append({"groups": d, "rank": d-1, "sat_status": sat["status"],
                     "flipped_status": neg["status"], "transitions_per_run": 0})
    return rows


def run_experiment():
    rng = random.Random(SEED)
    cases = [(0, []), (0, [()]), (2, []), (1, [(1,), (-1,)]),
             (3, [(1, 2, 3), (-1, -2, -3)]), (1, [(1, 1, 1), (-1, -1, -1)]),
             (4, [(-1, -2, -2), (-3, 1), (2, -2, 1)])]
    ncontrols = len(cases)
    for _ in range(60):
        n = rng.randint(1, 5)
        cases.append((n, [tuple(rng.randint(1, n)*rng.choice((-1, 1))
                                for _ in range(rng.randint(1, 3)))
                          for _ in range(rng.randint(0, 4))]))
    summary = {"oracle_cases": len(cases), "seeded_cases": len(cases)-ncontrols,
               "controls": ncontrols, "source_assignments_checked": 0,
               "source_models_lifted": 0, "sat_cases": 0, "unsat_cases": 0,
               "images_requiring_transitions": 0, "max_transitions_observed": 0,
               "max_support_cardinality": 0, "weight_two_models_lifted": 0,
               "weight_two_max_mask_weight": 0, "weight_two_max_transitions": 0,
               "weight_two_images_requiring_transitions": 0}
    examples = []
    for k, (n, clauses) in enumerate(cases):
        reduction = three_cnf_to_ternary_supports(tuple(f"x{i}" for i in range(n)), clauses)
        models = raw_models(n, clauses)
        active = sum(1 << i for i, v in enumerate(reduction.variable_masks) if v)
        t = sum(map(len, clauses))
        require(len(reduction.supports) == n + len(clauses) + t and
                all(len(s) <= 3 and all(0 <= x < 1 << (2*t) for x in s)
                    for s in reduction.supports), "Size bound")
        bounded = three_cnf_to_weight_two_supports(reduction.original_variables, clauses)
        require(len(bounded.supports) == 2*t + len(clauses) and bounded.n_coordinates <= 3*t,
                "Bounded variant dimensions")
        owners = [set() for _ in range(bounded.n_coordinates)]
        for i, support in enumerate(bounded.supports):
            require(len(support) <= 3, "Too many bounded options")
            for x in support:
                weight = x.bit_count()
                require(weight <= 2 and x < 1 << bounded.n_coordinates, "Mask weight or extent")
                summary["weight_two_max_mask_weight"] = max(summary["weight_two_max_mask_weight"], weight)
                while x:
                    bit = x & -x
                    owners[bit.bit_length()-1].add(i)
                    x ^= bit
        require(all(len(s) == 2 for s in owners), "Each coordinate touches exactly two groups")
        for model in models:
            chosen = reduction.lift_witness(model)
            require(reduce(xor, chosen, 0) == 0 and
                    all(x in s for x, s in zip(chosen, reduction.supports)) and
                    reduction.project_witness(chosen) == model & active, "Source lift")
            chosen = bounded.lift_witness(model)
            require(reduce(xor, chosen, 0) == 0 and
                    all(x in s for x, s in zip(chosen, bounded.supports)) and
                    bounded.project_witness(chosen) == model & active, "Weight-two source lift")
        result = decide_ternary_reduction(reduction)
        bresult = decide_ternary_reduction(bounded)
        require(result["status"] == ("SAT" if models else "UNSAT"), "Decision oracle")
        require(bresult["status"] == result["status"], "Weight-two source oracle")
        if models:
            require(result["source_witness_mask"] in models, "Projected model")
            require(bresult["source_witness_mask"] in models, "Bounded projected model")
        else:
            require(result["source_witness_mask"] is None, "Spurious projected model")
            require(bresult["source_witness_mask"] is None, "Spurious bounded model")
        summary["source_assignments_checked"] += 1 << n
        summary["source_models_lifted"] += len(models)
        summary["weight_two_models_lifted"] += len(models)
        summary["sat_cases" if models else "unsat_cases"] += 1
        summary["images_requiring_transitions"] += int(result["transitions"] > 0)
        summary["weight_two_images_requiring_transitions"] += int(bresult["transitions"] > 0)
        summary["weight_two_max_transitions"] = max(summary["weight_two_max_transitions"],
                                                    bresult["transitions"])
        summary["max_transitions_observed"] = max(summary["max_transitions_observed"],
                                                  result["transitions"])
        summary["max_support_cardinality"] = max(summary["max_support_cardinality"],
                                                 max(map(len, reduction.supports), default=0))
        if k < ncontrols:
            examples.append({"source_variables": n, "source_cnf": clauses, "coordinates": 2*t,
                             "groups": len(reduction.supports), "decision": result["status"],
                             "transitions": result["transitions"], "peak_states": result["peak_states"],
                             "source_witness_mask": result["source_witness_mask"],
                             "weight_two_coordinates": bounded.n_coordinates,
                             "weight_two_groups": len(bounded.supports),
                             "weight_two_transitions": bresult["transitions"],
                             "weight_two_witness_mask": bresult["source_witness_mask"]})
    red = three_cnf_to_ternary_supports(("a", "b", "c"), ((1, 2, 3),))
    checked = valid = 0
    projected = set()
    for chosen in product(*red.supports):
        checked += 1
        if reduce(xor, chosen, 0) == 0:
            valid += 1
            projected.add(red.project_witness(chosen))
    require((checked, valid, projected) == (648, 12, set(range(1, 8))), "Target oracle")
    return {"schema_version": 1, "all_checks_passed": True, "seed": SEED,
            "scope": "Finite controls for the <=2-choice Gaussian case, the <=3-choice decision reduction and its <=2-Hamming-weight variant. Both encodings are checked separately against the same source oracle; source model counts are not preserved. The all-input claims use the mathematical proof.",
            "binary_even_span_controls": binary_cases(), "ternary_controls": examples,
            "one_clause_target_oracle": {"tuples_checked": checked, "zero_xor_tuples": valid,
                                         "distinct_projected_source_models": len(projected)},
            "summary": summary}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    result = run_experiment()
    (out / "ternary_support_threshold.json").write_text(json.dumps(result, indent=2, sort_keys=True)
                                                        + "\n", encoding="utf-8")
    print(json.dumps(result["summary"], indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
