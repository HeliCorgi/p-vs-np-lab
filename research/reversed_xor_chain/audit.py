"""Independent clause-level audit of reversed XOR-chain resolution certificates.

Only stdlib; XOR source clauses and resolution inference are reconstructed
independently from generate.py. Every proof line is replayed, and small CNFs
are checked against all full assignments.
"""
from __future__ import annotations

import copy
import hashlib
import itertools
import json
from pathlib import Path
import sys

from generate import SIZES, certificate

REPORT = Path(__file__).resolve().parents[2] / "results" / "reversed_xor_chain.json"


class BadProof(ValueError):
    pass


def source_from_truth_table(m):
    """Do not reuse the generator's source clause construction."""
    states = []
    for i in range(m):
        x = i + 1
        p = m + 1 + i
        q = 2 * m + 2 + i
        # Inputs are (p_i,x_i,p_(i+1)) and (x_i,s_(i+1),s_i).
        for a, b, out in ((p, x, p + 1), (x, q + 1, q)):
            for mask in range(8):
                bits = ((mask >> 2) & 1, (mask >> 1) & 1, mask & 1)
                if bits[2] == bits[0] ^ bits[1]:
                    continue
                states.append(frozenset(
                    -var if bit else var
                    for var, bit in zip((a, b, out), bits)
                ))
    states.extend([
        frozenset((-(m + 1),)),
        frozenset((-(3 * m + 2),)),
        frozenset((2 * m + 1,)),
        frozenset((-(2 * m + 2),)),
    ])
    return states


def independent_check(m, lines):
    if m < 1 or len(lines) != (8 * m + 4) + (10 * m - 2):
        raise BadProof("wrong proof size")
    boundary = 8 * m + 4
    expected = source_from_truth_table(m)
    if len(set(expected)) != boundary:
        raise BadProof("duplicated expected source")
    actual_source = []
    previous = []
    pivot_histories = []  # union of all pivot variables on any ancestor path
    for index, item in enumerate(lines):
        clause = item.get("clause")
        if not isinstance(clause, list) or any(
            not isinstance(v, int) or isinstance(v, bool) or v == 0
            or abs(v) > 3 * m + 2 for v in clause
        ):
            raise BadProof("invalid literal type/index")
        current = frozenset(clause)
        if len(current) != len(clause) or any(-v in current for v in current):
            raise BadProof("duplicate literal or tautology")
        if len(current) > 3:
            raise BadProof("width exceeds three")
        if index < boundary:
            if item.get("kind") != "axiom" or set(item) != {"kind", "clause"}:
                raise BadProof("malformed axiom")
            actual_source.append(current)
        else:
            if item.get("kind") != "resolve" or set(item) != {
                "kind", "clause", "parents", "pivot"
            }:
                raise BadProof("malformed inference")
            parents = item.get("parents")
            pivot = item.get("pivot")
            if not isinstance(parents, list) or len(parents) != 2 or not isinstance(pivot, int) or pivot <= 0:
                raise BadProof("bad parents or pivot")
            if any(not isinstance(j, int) or isinstance(j, bool) or j < 0 or j >= index for j in parents):
                raise BadProof("forward or invalid parent reference")
            left, right = (previous[j] for j in parents)
            used_on_ancestor_path = set(pivot_histories[parents[0]]) | set(pivot_histories[parents[1]])
            if pivot in used_on_ancestor_path:
                raise BadProof("nonregular resolution: pivot was already used on an ancestor path")
            if pivot in left and -pivot in right:
                pass
            elif -pivot in left and pivot in right:
                pass
            else:
                raise BadProof("missing complementary pivot pair")
            # Strict ordinary resolution: all other parent literals must survive.
            outcome = (left | right) - {pivot, -pivot}
            if current != outcome:
                raise BadProof("incorrect exact resolvent")
        previous.append(current)
        if index < boundary:
            pivot_histories.append(frozenset())
        else:
            pivot_histories.append(frozenset(used_on_ancestor_path | {pivot}))
    if set(actual_source) != set(expected):
        raise BadProof("input clauses do not match fresh truth-table encoding")
    if previous[-1] != frozenset():
        raise BadProof("no empty-clause refutation")
    return True


def clause_true(clause, assignment):
    return any(assignment[abs(lit) - 1] == (lit > 0) for lit in clause)


def complete_assignment_checks(m, lines):
    """Only m<=3; completely scan all 2^(3m+2) possible assignments."""
    assert 1 <= m <= 3
    ax = [line["clause"] for line in lines[:8 * m + 4]]
    total = 1 << (3 * m + 2)
    for bits in itertools.product((False, True), repeat=3 * m + 2):
        if all(clause_true(c, bits) for c in ax):
            raise BadProof("satisfying assignment to contradictory miter")
    return total


def aligned_model_check(m, lines):
    """Both circuits evaluate the same parity; aligned output has a model."""
    ax = [list(line["clause"]) for line in lines[:8 * m + 4]]
    ax[-1] = [2 * m + 2]  # s_0 = 1 instead of s_0 = 0
    bits = [False] * (3 * m + 2)
    bits[0] = True       # x_0=1, all other x_i=0
    prefix = 0
    for i in range(m + 1):
        bits[m + i] = bool(prefix)  # p_i
        if i < m:
            prefix ^= int(bits[i])
    suffix = 0
    for i in reversed(range(m + 1)):
        bits[2 * m + 1 + i] = bool(suffix)  # s_i
        if i > 0:
            suffix ^= int(bits[i - 1])
    if not all(clause_true(cl, bits) for cl in ax):
        raise BadProof("aligned-output positive control has no explicit model")
    return True


def corruption_checks():
    m = 2
    original = certificate(m)
    first = 8 * m + 4
    mutators = [
        lambda p: p[0].update(clause=[1]),
        lambda p: p[first].update(pivot=999),
        lambda p: p[first].update(parents=[first, 0]),
        lambda p: p[first].update(clause=[1]),
    ]
    rejected = 0
    for mutate in mutators:
        broken = copy.deepcopy(original)
        mutate(broken)
        try:
            independent_check(m, broken)
        except BadProof:
            rejected += 1
        else:
            raise BadProof("mutated invalid proof passed independent replay")
    return rejected


def result():
    cases = []
    total_full = 0
    for m in SIZES:
        lines = certificate(m)
        independent_check(m, lines)
        total_full += complete_assignment_checks(m, lines) if m <= 3 else 0
        aligned_model_check(m, lines)
        serialized = json.dumps(lines, sort_keys=True, separators=(",", ":")).encode()
        cases.append({
            "m": m,
            "variables": 3 * m + 2,
            "source_clauses": 8 * m + 4,
            "derived_lines": 10 * m - 2,
            "width": 3,
            "certificate_sha256": hashlib.sha256(serialized).hexdigest(),
            "checked_lines": len(lines),
            "aligned_output_sat": True,
            "regular": True
        })
    return {
        "schema_version": 1,
        "paper_theorem": "For every m>=1, reversed XOR parity chain miter has a width<=3 strict ordinary resolution refutation with exactly 10m-2 derived lines.",
        "general_P_vs_NP_result": False,
        "new_Lean_formalization": False,
        "full_assignment_cutoff_m": 3,
        "full_assignments_checked": total_full,
        "rejected_corruptions": corruption_checks(),
        "regularity_audited": True,
        "cases": cases
    }


if __name__ == "__main__":
    report = result()
    encoded = json.dumps(report, sort_keys=True, indent=2, ensure_ascii=False) + "\n"
    if "--check" in sys.argv:
        if not REPORT.exists() or REPORT.read_text(encoding="utf-8") != encoded:
            raise SystemExit("Recorded report differs from independently recomputed audit")
        print("PASS: independent replay, exhaustive controls, 4 corruptions, reproducible report")
    elif "--write" in sys.argv:
        REPORT.parent.mkdir(parents=True, exist_ok=True)
        REPORT.write_text(encoded, encoding="utf-8")
        print(str(REPORT))
    else:
        print(encoded, end="")
