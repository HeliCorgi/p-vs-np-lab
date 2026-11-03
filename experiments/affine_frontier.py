#!/usr/bin/env python3
"""Measure exact signature support decisions, including a connected 3SAT bridge image.

Run with PYTHONPATH=src python experiments/affine_frontier.py --out-dir results.
All reported work units are deterministic counters, not elapsed time.
"""

from __future__ import annotations

import argparse
from functools import reduce
import hashlib
import json
from operator import xor
from pathlib import Path
import random

from pnp_lab.block_bridge import three_cnf_to_constant_blocks


SEED = 7070511
COUNTERS = ("transitions", "peak_states", "affine_groups", "affine_rank",
            "residual_groups", "elimination_rounds", "suffix_pruned",
            "projection_visits", "peak_cut_rank")


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def cnf_holds(clauses, mask):
    return all(any(bool(mask & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in clause) for clause in clauses)


def raw_tables(reduction):
    """Enumerate only one group at a time. Map each signature to a real target assignment.

    This independent adapter reads the actual target clauses and normalized XOR
    rows; it never calls the previous counter or the new affine elimination code.
    """
    bridge = reduction.bridge
    names = bridge.affine.variables
    index = {name: i for i, name in enumerate(names)}
    groups = [tuple(index[name] for name in group) for group in reduction.groups]
    group_of = {column: g for g, group in enumerate(groups) for column in group}
    require(len(group_of) == len(names) == sum(map(len, groups)), "Bad partition")
    local_clauses = [[] for _ in groups]
    for clause in bridge.cnf:
        if not clause:
            require(not groups and bridge.cnf == ((),), "Expected canonical false bridge")
            return [{}], 0, 0   # the empty clause becomes one empty support, hence no choice
        owners = {group_of[abs(lit) - 1] for lit in clause}
        require(len(owners) == 1, "Unexpected cross-group CNF")
        local_clauses[owners.pop()].append(clause)
    equations = bridge.affine.equations
    rhs_mask = sum(rhs << i for i, (_, rhs) in enumerate(equations))
    tables, visits = [], 0
    for columns, clauses in zip(groups, local_clauses):
        table = {}
        group_mask = sum(1 << col for col in columns)
        incident = [(i, row & group_mask) for i, (row, _) in enumerate(equations)
                    if row & group_mask]
        for bits in range(1 << len(columns)):
            visits += 1
            mask = sum(((bits >> j) & 1) << col for j, col in enumerate(columns))
            if cnf_holds(clauses, mask):
                signature = sum(((mask & row).bit_count() % 2) << i for i, row in incident)
                table.setdefault(signature, mask)
        tables.append(table)
    return tables, rhs_mask, visits


def decision(supports, rhs, budget=None):
    from pnp_lab.frontier import decide_signature_supports
    res = decide_signature_supports(supports, rhs, max_transitions=budget)
    choices = res["witness"]
    if res["status"] == "SAT":
        require(choices is not None and len(choices) == len(supports), "Bad choice count")
        require(all(s in options for options, s in zip(supports, choices)), "Illegal choice")
        require(reduce(xor, choices, 0) == rhs, "Incorrect choice parity")
    else:
        require(res["status"] in {"UNKNOWN", "UNSAT"} and choices is None,
                "Incomplete or negative result contains a witness")
    return res


def compact(res):
    return {k: res[k] for k in ("status", *COUNTERS)}


def solve_bridge(reduction, tables, rhs, order=None, budget=None):
    order = list(range(len(tables))) if order is None else order
    require(sorted(order) == list(range(len(tables))), "Not a group permutation")
    supports = [tuple(sorted(tables[g])) for g in order]
    res = decision(supports, rhs, budget)
    projected = None
    if res["status"] == "SAT":
        # Supports discard multiplicities; a stored representative per local
        # signature suffices to reconstruct one full Boolean witness.
        target = sum(tables[g][s] for g, s in zip(order, res["witness"]))
        require(cnf_holds(reduction.bridge.cnf, target)
                and all((row & target).bit_count() % 2 == rhs_bit
                        for row, rhs_bit in reduction.bridge.affine.equations),
                "Returned choices do not lift to a raw target model")
        projected = reduction.project_witness(target)
        require(cnf_holds(reduction.original_cnf, projected), "Invalid projected source model")
    return res, projected


def small_oracle():
    rng = random.Random(SEED)
    formulas = [(0, ()), (0, ((),)), (3, ()), (2, ((1,), (-1,))),
                (4, ((1, -1, 3), (-3, 3))), (4, ((-1, -1, 2), (-2,), (-1,)))]
    for _ in range(80):
        n = rng.randint(1, 4)
        clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randint(1, 3)))
                        for _ in range(rng.randint(1, 4)))
        formulas.append((n, clauses))
    totals = {"cases": len(formulas), "random_cases": 80, "controls": 6, "source_visits": 0,
              "sat": 0, "unsat": 0, "source_witnesses_checked": 0,
              "max_transitions": 0, "max_peak_states": 0}
    rows = []
    for n, clauses in formulas:
        red = three_cnf_to_constant_blocks(tuple(f"x{i}" for i in range(n)), clauses)
        tables, rhs, visits = raw_tables(red)
        models = [s for s in range(1 << n) if cnf_holds(clauses, s)]
        res, projected = solve_bridge(red, tables, rhs)
        require(res["status"] == ("SAT" if models else "UNSAT"), "Source oracle mismatch")
        require(not models or projected in models, "Source witness mismatch")
        totals["source_visits"] += 1 << n
        totals[res["status"].lower()] += 1
        totals["source_witnesses_checked"] += int(projected is not None)
        totals["max_transitions"] = max(totals["max_transitions"], res["transitions"])
        totals["max_peak_states"] = max(totals["max_peak_states"], res["peak_states"])
        rows.append([n, clauses, len(models), projected, visits, *compact(res).values()])
    totals["case_digest_sha256"] = hashlib.sha256(
        json.dumps(rows, separators=(",", ":")).encode()).hexdigest()
    totals["digest_fields_in_order"] = ["n", "clauses", "source_count", "source_witness_mask",
                                         "local_visits", "status", *COUNTERS]
    return totals


def pure_affine_family():
    cases = []
    for m in (1, 4, 12, 32, 64, 128):
        variables = tuple(f"x{i}" for i in range(3 * m))
        clauses = tuple((3*i+1, 3*i+2, 3*i+3) for i in range(m))
        red = three_cnf_to_constant_blocks(variables, clauses)
        tables, rhs, visits = raw_tables(red)
        res, _ = solve_bridge(red, tables, rhs, budget=0)
        require(visits == 12 * m and all(len(t) == 2 for t in tables), "Bad disjoint image")
        require(res["status"] == "SAT" and res["transitions"] == 0, "Unexpected search")
        require(res["affine_groups"] == 3 * m and res["affine_rank"] == m,
                "Disjoint affine groups were not absorbed")
        cases.append({"m": m, "source_variables": 3*m, "target_variables": 6*m,
                      "local_assignment_visits": visits, **compact(res),
                      "previous_counter_predicted_peak": 2**m,
                      "previous_counter_predicted_join_products": 10*(2**m-1)})
    return cases


def cycle_image(length, positive_sibling=False):
    names = tuple(f"x{i}" for i in range(length))
    pos = tuple((1+i, 1+(i+1) % length) for i in range(length))
    second = (tuple(c + (1+(i+2) % length,) for i, c in enumerate(pos)) if positive_sibling
              else tuple(tuple(-v for v in c) for c in pos))
    return three_cnf_to_constant_blocks(names, pos + second)


def cycle_case(length, positive_sibling=False):
    red = cycle_image(length, positive_sibling)
    tables, rhs, visits = raw_tables(red)
    require(all(len(t) == 5 for t in tables), "Expected five-entry nonaffine supports")
    interleaved = [3*(i+offset)+j for i in range(length)
                   for offset in (0, length) for j in range(3)]
    expected = "SAT" if positive_sibling else "UNSAT"
    good, _ = solve_bridge(red, tables, rhs, order=interleaved)
    require(good["status"] == expected and good["affine_groups"] == 0
            and good["suffix_pruned"] > 0, "Interleaved image decision failed")
    if not positive_sibling:
        require(good["peak_cut_rank"] <= 20, "Proved interleaved cut-rank bound failed")
    budget = None if length <= 9 else 8000
    bad, _ = solve_bridge(red, tables, rhs, budget=budget)
    require(bad["status"] in {expected, "UNKNOWN"}, "Wrong native decision")
    half_cut = 3*length
    states_at_cut = (bad["state_counts"][half_cut] if len(bad["state_counts"]) > half_cut
                     else None)
    lower_bound = 1 << (length//2)
    if budget is None:
        require(bad["status"] == expected and states_at_cut is not None
                and states_at_cut >= lower_bound, "Predicted native-order cut not observed")
    else:
        require(bad["transitions"] <= budget, "Transition budget overrun")
    return {"length": length, "source_clauses": len(red.original_cnf),
            "target_variables": len(red.bridge.affine.variables),
            "xor_rows": len(red.bridge.affine.equations),
            "local_assignment_visits": visits, "groups": len(tables),
            "native_full_half_cut_lower_bound": lower_bound,
            "native_half_cut_states_observed": states_at_cut,
            "native_budget": budget, "native": compact(bad), "interleaved": compact(good)}


def grid_cases():
    """Finite SAT controls only; these samples do not quantify over group orders."""
    out = []
    for h in (2, 4):
        edges = []
        for row in range(h):
            for col in range(h):
                v = 1 + h*row + col
                if col+1 < h:
                    edges.append((v, v+1))
                if row+1 < h:
                    edges.append((v, v+h))
        red = three_cnf_to_constant_blocks(tuple(f"x{i}" for i in range(h*h)), edges)
        tables, rhs, _ = raw_tables(red)
        require(all(len(t) == 5 for t in tables), "Grid must have all nonaffine supports")
        perm = list(range(len(tables)))
        random.Random(SEED+h).shuffle(perm)
        for label, order in (("source_order", None), ("fixed_shuffle", perm)):
            res, _ = solve_bridge(red, tables, rhs, order, budget=100000)
            require(res["status"] in {"UNKNOWN", "SAT"}, "Positive-grid false UNSAT")
            out.append({"h": h, "source_clauses": len(edges), "groups": len(tables),
                        "order": label, "budget": 100000, **compact(res)})
    return out


def controls():
    cases = [
        ("affine_cascade", [(0, 1, 2), (0, 1)], 3, 0, "SAT"),
        ("affine_hull_contradiction", [(0, 3, 5, 6), (8,)], 9, 0, "UNSAT"),
        ("noncoordinate_suffix", [(0, 1, 2), (0, 3, 12)], 1, None, "SAT"),
        ("nonaffine_missing_value", [(0, 1, 2)], 3, None, "UNSAT"),
        ("missing_value_budget", [(0, 1, 2)], 3, 2, "UNKNOWN"),
        ("missing_value_exact_budget", [(0, 1, 2)], 3, 3, "UNSAT"),
    ]
    out = []
    for name, supports, rhs, budget, expected in cases:
        res = decision(supports, rhs, budget)
        require(res["status"] == expected, f"Unexpected {name} status")
        if name == "noncoordinate_suffix":
            require(res["suffix_pruned"] > 0, "No suffix affine pruning")
        if name == "affine_cascade":
            require(res["affine_groups"] == res["elimination_rounds"] == 2
                    and res["transitions"] == 0, "No cascade")
        out.append({"name": name, "supports": supports, "rhs": rhs, "budget": budget,
                    "witness": res["witness"], **compact(res)})
    return out


def run_experiment():
    oracle = small_oracle()
    disjoint = pure_affine_family()
    connected = [cycle_case(length) for length in (3, 5, 7, 9, 15, 31)]
    siblings = [cycle_case(length, True) for length in (5, 7)]
    grids = grid_cases()
    checks = controls()
    full = [c for c in connected if c["native"]["status"] == "UNSAT"]
    return {"schema_version": 1, "experiment": "affine_frontier", "random_seed": SEED,
            "input_language": "Choose one member per explicit support to realize a prescribed XOR. For bridge images each support is produced by raw local Boolean enumeration; SAT choices are lifted back and checked against original clauses.",
            "counter_scope": "Transitions count residual prefix-choice pairs only. Local enumeration, affine elimination, suffix bases, reconstruction, and integer bit costs are additional. This algorithm decides feasibility; previous signature counting returns exact counts, a different output.",
            "small_bridge_source_oracle": oracle,
            "disjoint_affine_bridge_images": disjoint,
            "disjoint_comparison_scope": "Old counts are formulas proved for the previous counter in docs/constant_block_bridge.md, not executions in this experiment. Its reported work includes counting all models.",
            "connected_order_barrier": connected,
            "connected_family": "For odd L, C_i=(x_i OR x_{i+1}) and D_i=(not x_i OR not x_{i+1}) on a cycle. Source order lists all C then all D. Together the clauses force alternation, impossible on an odd cycle. Interleaved order processes the corresponding C_i and D_i triples consecutively; constraints are identical.",
            "positive_siblings": siblings,
            "positive_sibling_family": "Replace D_i by E_i=(x_i OR x_{i+1} OR x_{i+2}). Each model of the positive prefix extends. The native half-cut lower bound now counts distinguishable genuinely completable prefixes.",
            "positive_grid_samples": grids,
            "grid_scope": "Positive binary clauses for horizontal and vertical edges of an h by h grid; every sample is satisfiable. Source-order and one reproducible permutation are finite observations, not an all-order experiment.",
            "barrier_scope": "See docs/affine_frontier.md for the all-size native-order lower bound: a full odd-cycle run retains at least 2^floor(L/2) states at the cut after the positive triples. Budgeted runs report only measured work up to UNKNOWN. The original odd-cycle SAT decision is easy. Interleaved residual cut ranks on the UNSAT family are bounded by 20; this is a bound for this family and order only.",
            "support_controls": checks,
            "summary": {"bridge_oracle_cases": oracle["cases"],
                        "bridge_oracle_source_assignments": oracle["source_visits"],
                        "bridge_oracle_sat": oracle["sat"], "bridge_oracle_unsat": oracle["unsat"],
                        "largest_disjoint_m": disjoint[-1]["m"],
                        "largest_disjoint_absorbed_groups": disjoint[-1]["affine_groups"],
                        "largest_disjoint_transitions": disjoint[-1]["transitions"],
                        "connected_full_native_max_length": max(c["length"] for c in full),
                        "connected_full_native_max_peak_states": max(c["native"]["peak_states"] for c in full),
                        "connected_full_native_max_transitions": max(c["native"]["transitions"] for c in full),
                        "connected_largest_length": connected[-1]["length"],
                        "connected_largest_interleaved_transitions": connected[-1]["interleaved"]["transitions"],
                        "connected_largest_interleaved_peak": connected[-1]["interleaved"]["peak_states"],
                        "connected_budget_unknown_cases": sum(c["native"]["status"] == "UNKNOWN" for c in connected),
                        "satisfiable_cycle_sibling_cases": len(siblings),
                        "positive_grid_order_samples": len(grids),
                        "support_controls": len(checks)},
            "all_checks_passed": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    out = parser.parse_args().out_dir
    report = run_experiment()
    out.mkdir(exist_ok=True, parents=True)
    (out / "affine_frontier.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": True, **report["summary"]}, sort_keys=True))


if __name__ == "__main__":
    main()
