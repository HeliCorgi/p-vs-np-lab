#!/usr/bin/env python3
"""Ordinary resolution refutations of opposite-output identical Tseitin circuits.

The refutation is a line-by-line width-3 resolution certificate, not a RUP
shortcut and not a claim about the complexity of arbitrary CNFs. No solver
search; finite semantic enumeration is hard-capped at m=1,2.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

if __package__:
    from experiments.tseitin_affine_lift import build_cnf, eval_clause, extension
else:
    from tseitin_affine_lift import build_cnf, eval_clause, extension


def canonical(clause):
    """Sorted signed DIMACS literals; tautological clauses are not permitted."""
    s = set(clause)
    if 0 in s or any(-lit in s for lit in s):
        raise ValueError("zero literal or tautological clause")
    return tuple(sorted(s, key=lambda lit: (abs(lit), lit < 0)))


def xor_clauses(a, b, c):
    return ((a, b, -c), (a, -b, c), (-a, b, c), (-a, -b, -c))


def miter(m):
    """Two copies share original x,y but have disjoint AND/XOR gate variables."""
    if m < 1:
        raise ValueError("m must be >= 1")
    original_n, original, _ = build_cnf(m)
    offset = 2 * m - 1
    gate_clauses = original[:-1]
    def second_copy(clause):
        return tuple((1 if lit > 0 else -1) *
                     (abs(lit) + (offset if abs(lit) > 2*m else 0))
                     for lit in clause)
    last_a = original[-1][0]
    last_b = last_a + offset
    axioms = tuple(map(canonical, gate_clauses +
                       tuple(second_copy(c) for c in gate_clauses) +
                       ((last_a,), (-last_b,))))
    assert original_n + offset == 6*m - 2
    assert len(axioms) == 14*m - 6
    return 6*m-2, axioms


def certificate(m):
    """Generate a fully explicit two-parent ordinary-resolution proof.

    Input axioms occupy indices 0..len(axioms)-1. Each step is indexed after
    all axioms. A step specifies left/right parent, signed pivot and resolvent.
    No weakening, XOR or derived-gate assumptions are admitted.
    """
    nvars, axioms = miter(m)
    lines = list(axioms)
    axiom_id = {c: j for j, c in enumerate(axioms)}
    steps = []

    def source(clause):
        return axiom_id[canonical(clause)]

    def resolve(left, right, pivot):
        a, b = set(lines[left]), set(lines[right])
        if pivot not in a or -pivot not in b:
            raise AssertionError("internal invalid pivot")
        output = canonical((a | b) - {pivot, -pivot})
        line_id = len(lines)
        lines.append(output)
        steps.append({"left": left, "right": right, "pivot": pivot,
                      "clause": list(output)})
        return line_id

    x = [i+1 for i in range(m)]
    y = [m+i+1 for i in range(m)]
    p = [2*m+i+1 for i in range(m)]
    t = [3*m+i for i in range(1, m)]
    offset = 2*m-1
    pb = [z+offset for z in p]
    tb = [z+offset for z in t]

    # Each AND pair yields (-pA OR pB) and (-pB OR pA)
    # with two ordinary resolution steps per implication.
    equal = {}
    for i in range(m):
        a, b = p[i], pb[i]
        q = resolve(source((-a,x[i])), source((b,-x[i],-y[i])), x[i])
        ab = resolve(q, source((-a,y[i])), -y[i])
        q = resolve(source((-b,x[i])), source((a,-x[i],-y[i])), x[i])
        ba = resolve(q, source((-b,y[i])), -y[i])
        equal[(a,b)] = (ab,ba)

    # Inductive XOR-gate comparison. Rewrite the B gate's 4 clauses
    # to the A inputs, with 2 resolution steps per clause (8 steps).
    # Then 3 + 3 steps establish both output implications.
    for i in range(1, m):
        a = p[0] if i == 1 else t[i-2]
        ap = pb[0] if i == 1 else tb[i-2]
        b, bp = p[i], pb[i]
        c, cp = t[i-1], tb[i-1]
        A = [source(C) for C in xor_clauses(a,b,c)]
        B = []
        for C in xor_clauses(ap,bp,cp):
            current = source(C)
            for old, new in ((ap,a),(bp,b)):
                old_literal = old if old in C else -old
                # (-old' OR new) is one of the already derived implications.
                link = equal[(new,old)][1 if old_literal > 0 else 0]
                assert lines[link] == canonical((-old_literal,
                                                  new if old_literal > 0 else -new))
                current = resolve(current, link, old_literal)
            B.append(current)

        q0 = resolve(A[0], B[1], b)
        q1 = resolve(B[2], A[3], b)
        ab = resolve(q0, q1, a)  # (-c OR cp)
        q0 = resolve(B[0], A[1], b)
        q1 = resolve(A[2], B[3], b)
        ba = resolve(q0, q1, a)  # (c OR -cp)
        equal[(c,cp)] = (ab,ba)

    last_a = p[0] if m == 1 else t[-1]
    last_b = pb[0] if m == 1 else tb[-1]
    q = resolve(source((last_a,)), equal[(last_a,last_b)][0], last_a)
    resolve(q, source((-last_b,)), last_b)
    assert lines[-1] == ()
    assert len(steps) == 18*m-12
    return {"m": m, "variables": nvars, "axioms": [list(c) for c in axioms],
            "steps": steps}


def check_certificate(proof):
    """Generic syntax-only resolution checker: independent of gate semantics."""
    n = proof["variables"]
    axioms = [canonical(c) for c in proof["axioms"]]
    lines = list(axioms)
    if not axioms or any(not c for c in axioms):
        raise ValueError("invalid input clauses")
    if any(abs(v) > n for c in axioms for v in c):
        raise ValueError("out-of-range input literal")
    for step in proof["steps"]:
        left, right, pivot = step["left"], step["right"], step["pivot"]
        if not (0 <= left < len(lines) and 0 <= right < len(lines)):
            raise ValueError("future or missing parent")
        if pivot == 0 or abs(pivot) > n:
            raise ValueError("invalid pivot")
        a, b = set(lines[left]), set(lines[right])
        if pivot not in a or -pivot not in b:
            raise ValueError("not an ordinary resolution step")
        want = canonical((a | b) - {pivot, -pivot})
        if tuple(step["clause"]) != want:
            raise ValueError("incorrect resolvent")
        if len(want) > 3:
            raise ValueError("width exceeds three")
        lines.append(want)
    if lines[-1] != ():
        raise ValueError("not a refutation")
    return {"derived": len(proof["steps"]), "max_width": max(map(len,lines)),
            "all_lines": len(lines)}


def finite_semantic_control(m):
    """Independent raw-clause enumeration, never called above m=2."""
    if not 1 <= m <= 2:
        raise ValueError("semantic truth-table budget: m=1,2 only")
    n, axioms = miter(m)
    positive_copy = axioms[:-1] + (tuple([-axioms[-1][0]]),)
    unsat = 0
    sibling_sat = 0
    for bits in range(1 << n):
        unsat += all(eval_clause(clause,bits) for clause in axioms)
        sibling_sat += all(eval_clause(clause,bits) for clause in positive_copy)
    # Independently construct one satisfying assignment for the sibling.
    original = extension(m, 1 | (1 << m))
    gate_bits = original >> (2*m)
    both = original | (gate_bits << (4*m-1))
    assert all(eval_clause(c,both) for c in positive_copy)
    assert unsat == 0
    assert sibling_sat == (2**m-1)*2**(m-1)
    return {"enumerated_assignments": 1 << n, "miter_models": unsat,
            "same_output_sibling_models": sibling_sat,
            "constructive_sibling_model": both}


def verify(m):
    proof = certificate(m)
    stats = check_certificate(proof)
    assert proof["variables"] == 6*m-2
    assert len(proof["axioms"]) == 14*m-6
    assert stats["derived"] == 18*m-12
    assert stats["max_width"] <= 3
    payload = json.dumps({"axioms": proof["axioms"], "steps": proof["steps"]},
                         sort_keys=True, separators=(",",":"))
    return {"m":m, "variables":proof["variables"], "input_clauses":len(proof["axioms"]),
            "derived_resolution_lines":stats["derived"], "total_proof_lines":stats["all_lines"],
            "maximum_clause_width":stats["max_width"],
            "positive_half_affine_cover":(1<<m)-1,
            "certificate_sha256":hashlib.sha256(payload.encode("utf-8")).hexdigest(),
            "semantic_control":finite_semantic_control(m) if m <= 2 else None}


def report():
    return {"scope":"ordinary resolution, specific opposite-output double-copy Tseitin miter",
            "proof_scope":"uniform mathematical template plus independently checkable finite generated certificates",
            "general_sat_lower_bound":False, "new_lean_theorems":0,
            "finite_truth_table_cap_m":2,
            "cases":[verify(m) for m in (1,2,3,7,16)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=None)
    args = parser.parse_args()
    output = json.dumps(report(), ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if args.out_dir is None:
        print(output, end="")
    else:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / "tseitin_resolution_miter.json").write_text(output, encoding="utf-8")


if __name__ == "__main__":
    main()
