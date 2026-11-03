#!/usr/bin/env python3
"""Compare perfect matching and explicit frontiers on Hamming-weight-one XOR choices.

Run in the lab as PYTHONPATH=src python experiments/unit_support_matching.py --out-dir results.
The larger frontier rows use a transition budget and never infer UNSAT from a cutoff.
"""

from __future__ import annotations

import argparse
from functools import reduce
import json
from operator import xor
from pathlib import Path

from pnp_lab.frontier import decide_signature_supports
from pnp_lab.unit_matching import decide_unit_supports


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def check_witness(groups, rhs, result):
    witness = result["witness"]
    if result["status"] == "SAT":
        require(witness is not None and len(witness) == len(groups), "Wrong witness length")
        require(all(x in group for group, x in zip(groups, witness)), "Invalid original choice")
        require(reduce(xor, witness, 0) == rhs, "Witness did not attain the original XOR")
    else:
        require(witness is None, "Negative or unknown result returned choices")


def replicated(m, budget):
    star = 1 << m
    choices = [(0, 1 << i, star) for i in range(m)]
    groups = choices + choices
    matched = decide_unit_supports(groups, 0)
    direct = decide_signature_supports(groups, 0, max_transitions=budget)
    check_witness(groups, 0, matched)
    check_witness(groups, 0, direct)
    require(matched["status"] == "SAT" and 2*matched["matching_edges"] == matched["graph_vertices"],
            "Expected perfect matching")
    require(matched["graph_vertices"] == 8*m and matched["graph_edges"] == 4*m*m+5*m,
            "Unexpected graph size for replicated triples")
    require(direct["affine_groups"] == 0, "Three-element nonaffine group was eliminated")
    at_split = direct["state_counts"][m] if len(direct["state_counts"]) > m else None
    expected_states = 2**(m+1) - 1
    if budget is None:
        require(direct["status"] == "SAT" and at_split == expected_states
                and direct["peak_states"] == expected_states, "Unbudgeted state formula failed")
    else:
        require(direct["status"] == "UNKNOWN" and direct["transitions"] == budget,
                "Expected a genuine frontier cutoff")
    frontier = {k: direct[k] for k in ("status", "transitions", "peak_states",
                                         "peak_cut_rank", "affine_groups", "reason")}
    return {"m": m, "groups": len(groups), "rhs": 0, "star_mask": star,
            "predicted_full_middle_and_peak_states": expected_states,
            "observed_middle_states": at_split, "frontier_budget": budget,
            "frontier": frontier, "matching": matched}


def controls():
    d = 24
    groups = [(0, *(1 << ((i+j) % d) for j in (0, 1, 2))) for i in range(d)]
    rhs = sum(1 << i for i in range(1, d, 2))
    # An independent planted selection on the original supports makes the answer known.
    planted = [1 << i if i % 2 else 0 for i in range(d)]
    check_witness(groups, rhs, {"status": "SAT", "witness": planted})
    positive = decide_unit_supports(groups, rhs)
    require(positive["status"] == "SAT", "Failed known nonzero target")
    check_witness(groups, rhs, positive)

    d = 12
    groups = [tuple(1 << (b*d + (i+j) % d) for j in range(3))
              for b in range(2) for i in range(d)]
    rhs2 = 1 | (1 << d)
    # Exactly d nonzero units are chosen separately in each coordinate block.
    # The popcount of that block's XOR must therefore have parity d mod 2.
    for b in range(2):
        rhs_bits = (rhs2 >> (b*d)) & ((1 << d)-1)
        require(rhs_bits.bit_count() % 2 != d % 2, "Missing parity contradiction")
    negative = decide_unit_supports(groups, rhs2)
    require(negative["status"] == "UNSAT" and 2*negative["matching_edges"] < negative["graph_vertices"],
            "Failed known two-block contradiction")
    check_witness(groups, rhs2, negative)
    return {"positive": {"name": "overlapping_cyclic_units", "dimension": 24, "rhs": rhs,
                         "definition": "Group i offers 0 or e_i,e_(i+1),e_(i+2) modulo 24. Target sets every odd coordinate. Choosing e_i for odd i and 0 otherwise is an independent witness.",
                         "matching": positive},
            "negative": {"name": "two_odd_demand_components", "block_width": 12, "rhs": rhs2,
                         "definition": "Two disjoint 12-coordinate blocks; each has 12 cyclic groups of 3 consecutive unit choices, no zero. Target requests the first coordinate in each block. Each block has even selection count but odd target weight.",
                         "matching": negative}}


def run_experiment():
    examples = [replicated(m, None if m <= 8 else 8000) for m in (4, 8, 16, 24)]
    control = controls()
    completed = [r for r in examples if r["frontier"]["status"] == "SAT"]
    return {"schema_version": 1, "experiment": "unit_support_matching",
            "replicated_family": "Two consecutive copies of S_i={0,e_i,e_star}, i=0..m-1, target zero; star coordinate m touches every group. All supports have three members and are nonaffine. The input is satisfiable, for example by all zeros.",
            "all_size_explanation": "At the cut between copies any prefix selection is extendible by repeating those same choices. For each subset T of private units, if T omits any index its omitted groups can set either star parity, while for T full only parity 0 is possible. Hence exactly 2^(m+1)-1 distinct middle states. Earlier cuts have at most 2^(j+1)-1 states after j<m groups; after the split closed private bits are fixed and at most m coordinate bits remain free. This is an order-specific lower bound for this explicit frontier, not intrinsic hardness.",
            "counter_scope": "Transitions and peak states refer only to the supplied frontier order. Matching counts graph vertices, edges, searches and neighbor scans including blossom contractions; they are different work units, not timings. Larger frontiers stop at UNKNOWN; full middle counts are predictions, never measurements after an unfinished cut.",
            "replicated_cases": examples, "controls": control,
            "summary": {"replicated_cases": len(examples),
                        "all_matching_sat": all(r["matching"]["status"] == "SAT" for r in examples),
                        "largest_m": examples[-1]["m"],
                        "largest_matching_vertices": examples[-1]["matching"]["graph_vertices"],
                        "largest_matching_edges_in_graph": examples[-1]["matching"]["graph_edges"],
                        "largest_measured_complete_frontier_peak": max(r["frontier"]["peak_states"]
                                                                      for r in completed),
                        "largest_measured_complete_m": max(r["m"] for r in completed),
                        "budgeted_unknown": sum(r["frontier"]["status"] == "UNKNOWN" for r in examples),
                        "nonzero_positive_target_checked": True, "two_cluster_unsat_checked": True},
            "all_checks_passed": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    out = parser.parse_args().out_dir
    report = run_experiment()
    out.mkdir(parents=True, exist_ok=True)
    (out / "unit_support_matching.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": True, **report["summary"]}, sort_keys=True))


if __name__ == "__main__":
    main()
