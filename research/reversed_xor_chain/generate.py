"""Deterministic strict ordinary-resolution proof for opposite-order XOR chains.

No SAT oracle, weakening, semantic resolution, or extra extension variables.
See docs/reversed_xor_chain_resolution.md. Run with Python 3.10+.
"""
from __future__ import annotations

import hashlib
import itertools
import json

SIZES = (1, 2, 3, 5, 8)


def canon(literals):
    vals = set(literals)
    if 0 in vals or any(-v in vals for v in vals):
        raise ValueError("zero literal or tautological clause")
    return tuple(sorted(vals, key=lambda lit: (abs(lit), lit < 0)))


def xor_axioms(u, v, w):
    """Four clauses expressing w = u XOR v, in truth-table order."""
    clauses = []
    for bits in itertools.product((0, 1), repeat=3):
        if bits[2] == (bits[0] ^ bits[1]):
            continue
        clauses.append(canon(var if bit == 0 else -var
                             for var, bit in zip((u, v, w), bits)))
    assert len(clauses) == 4
    return clauses


def variable_layout(m):
    if m < 1:
        raise ValueError("m must be positive")
    return ([i + 1 for i in range(m)],
            [m + 1 + i for i in range(m + 1)],
            [2 * m + 2 + i for i in range(m + 1)])


def axiom_clauses(m):
    x, p, s = variable_layout(m)
    clauses = []
    for i in range(m):
        clauses.extend(xor_axioms(p[i], x[i], p[i + 1]))
        clauses.extend(xor_axioms(x[i], s[i + 1], s[i]))
    clauses.extend([canon((-p[0],)), canon((-s[m],)),
                    canon((p[m],)), canon((-s[0],))])
    assert len(clauses) == 8 * m + 4
    return clauses


def certificate(m):
    """Construct every original clause and every strict resolution inference.

    The exact source clauses are returned as input lines with no parents.
    Later lines store two earlier parent indices and a positive pivot.
    """
    x, p, s = variable_layout(m)
    lines = [{"clause": list(cl), "kind": "axiom"} for cl in axiom_clauses(m)]
    lookup = {tuple(line["clause"]): j for j, line in enumerate(lines)}

    def pick(*lits):
        cl = canon(lits)
        if cl not in lookup:
            raise AssertionError("missing previously derived clause: " + repr(cl))
        return lookup[cl]

    def resolve(first, second, pivot):
        if first >= len(lines) or second >= len(lines) or first < 0 or second < 0:
            raise AssertionError("invalid parent reference")
        left, right = (set(lines[j]["clause"]) for j in (first, second))
        if pivot in left and -pivot in right:
            pass
        elif -pivot in left and pivot in right:
            left, right = right, left
        else:
            raise AssertionError("parents do not resolve on the specified pivot")
        result = canon((left | right) - {pivot, -pivot})
        index = len(lines)
        lines.append({"clause": list(result), "kind": "resolve",
                      "parents": [first, second], "pivot": pivot})
        lookup.setdefault(result, index)
        return index

    # First input: p_0 = s_0 = 0. Derive the two directions p_1 <-> s_1.
    a, b, z, c, d = p[0], s[0], x[0], p[1], s[1]
    u = resolve(pick(-b), pick(b, -z, d), b)
    v = resolve(pick(-a), pick(a, z, -c), a)
    resolve(u, v, z)                                  # -c or d
    u = resolve(pick(-b), pick(b, z, -d), b)
    v = resolve(pick(-a), pick(a, -z, c), a)
    resolve(u, v, z)                                  # c or -d

    # A constant ten-line local resolution template per further input.
    for i in range(1, m):
        a, b, z, c, d = p[i], s[i], x[i], p[i + 1], s[i + 1]
        eq_ab = pick(-a, b)
        eq_ba = pick(a, -b)
        t1 = resolve(eq_ba, pick(-a, -z, -c), a)
        t2 = resolve(t1, pick(-b, z, d), z)
        t3 = resolve(eq_ab, pick(a, z, -c), a)
        t4 = resolve(t3, pick(b, -z, d), z)
        resolve(t2, t4, b)                            # -c or d
        t6 = resolve(eq_ba, pick(-a, z, c), a)
        t7 = resolve(t6, pick(b, z, -d), b)
        t8 = resolve(eq_ab, pick(a, -z, c), a)
        t9 = resolve(t8, pick(-b, -z, -d), b)
        resolve(t7, t9, z)                            # c or -d

    # The propagated equality contradicts p_m=1 and s_m=0.
    last = resolve(pick(p[m]), pick(-p[m], s[m]), p[m])
    resolve(last, pick(-s[m]), s[m])
    assert lines[-1]["clause"] == []
    assert len(lines) - (8 * m + 4) == 10 * m - 2
    return lines


def digest(lines):
    raw = json.dumps(lines, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def summary():
    return {
        "schema_version": 1,
        "model": "opposite-order XOR Tseitin miter, strict ordinary resolution",
        "size_cutoff": list(SIZES),
        "lean_new_theorems": 0,
        "cases": [
            {
                "m": m,
                "variables": 3 * m + 2,
                "input_clauses": 8 * m + 4,
                "derived_lines": len(certificate(m)) - 8 * m - 4,
                "max_width": max(len(line["clause"]) for line in certificate(m)),
                "certificate_sha256": digest(certificate(m)),
            } for m in SIZES
        ],
    }


if __name__ == "__main__":
    print(json.dumps(summary(), sort_keys=True, indent=2))
