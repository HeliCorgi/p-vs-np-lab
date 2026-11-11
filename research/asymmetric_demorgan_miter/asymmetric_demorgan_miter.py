"""Construct strict resolution refutations for asymmetric De Morgan monotone-circuit miters.

Self-contained certificate generator, not a SAT solver. The independent checker
lives in asymmetric_demorgan_audit.py and does not call this module's resolver.
"""
from __future__ import annotations

import hashlib
import json
import random
from pathlib import Path


def normalized(*literals):
    return tuple(sorted(set(literals), key=lambda x: (abs(x), x < 0)))


def validate(n, gates):
    if n < 2 or not gates:
        raise ValueError('requires at least two inputs and one gate')
    for i, (op, a, b) in enumerate(gates):
        if op not in ('AND', 'OR') or not (1 <= a <= n + i and 1 <= b <= n + i) or a == b:
            raise ValueError('invalid gate, operands, or topological order')


def certificate(n, gates):
    """Return complete axioms and strict two-parent resolution certificate."""
    validate(n, gates)
    g = len(gates)
    axioms = []
    sources = []
    steps = []
    lines = []

    def ax(*lits):
        idx = len(lines)
        c = normalized(*lits)
        if not c or any(-x in c for x in c):
            raise ValueError('invalid source')
        axioms.append(c)
        lines.append(c)
        return idx

    def res(left, right, pivot):
        a, b = set(lines[left]), set(lines[right])
        if pivot not in a or -pivot not in b:
            raise AssertionError('invalid pivot/parents')
        c = normalized(*(a - {pivot}), *(b - {-pivot}))
        if len(c) > 3 or any(-x in c for x in c):
            raise AssertionError('wide or tautological resolvent')
        idx = len(lines)
        steps.append({'left': left, 'right': right, 'pivot': pivot, 'clause': list(c)})
        lines.append(c)
        return idx

    def bout(w):
        if w <= n:
            return w
        return n + g + 4 * (w - n - 1) + 4

    # All input clauses precede all derived lines.
    for i, (op, a, b) in enumerate(gates):
        p, u, v = n+i+1, bout(a), bout(b)
        s = n+g+4*i+1
        t, r, q = s+1, s+2, s+3
        if op == 'AND':
            A = [ax(-p, a), ax(-p, b), ax(p, -a, -b)]
        else:
            A = [ax(p, -a), ax(p, -b), ax(-p, a, b)]
        S = [ax(s, u), ax(-s, -u)]
        T = [ax(t, v), ax(-t, -v)]
        if op == 'AND':
            D = [ax(r, -s), ax(r, -t), ax(-r, s, t)]
        else:
            D = [ax(-r, s), ax(-r, t), ax(r, -s, -t)]
        Q = [ax(q, r), ax(-q, -r)]
        sources.append((A, S, T, D, Q))
    p = n+g
    q = bout(p)
    apos = ax(p)
    bneg = ax(-q)

    # Each previous gate has derived the *two* output-equivalence clauses.
    equalities = {}
    for i, (op, a, b) in enumerate(gates):
        p, u, v = n+i+1, bout(a), bout(b)
        s = n+g+4*i+1
        t, r, q = s+1, s+2, s+3
        A, S, T, D, Q = sources[i]

        def transported_pair(source_pair, original, transformed):
            if original == transformed:  # shared primary input
                return source_pair
            up, down = equalities[original]
            # 'down' is (original OR NOT transformed), 'up' is
            # (NOT original OR transformed).
            positive = res(source_pair[0], down, transformed)
            negative = res(source_pair[1], up, -transformed)
            return positive, negative

        sp, sn = transported_pair(S, a, u)
        tp, tn = transported_pair(T, b, v)
        if op == 'AND':
            x = res(D[2], sn, s)
            x = res(x, tn, t)
            x = res(x, Q[0], -r)
            x = res(x, A[0], -a)
            up = res(x, A[1], -b)
            y = res(Q[1], D[0], -r)
            y = res(y, sp, -s)
            z = res(Q[1], D[1], -r)
            z = res(z, tp, -t)
            y = res(A[2], y, -a)
            down = res(y, z, -b)
        else:
            x = res(D[0], sn, s)
            y = res(D[1], tn, t)
            x = res(A[2], x, a)
            x = res(x, y, b)
            up = res(x, Q[0], -r)
            z = res(Q[1], D[2], -r)
            z = res(z, sp, -s)
            z = res(z, tp, -t)
            z = res(z, A[0], a)
            down = res(z, A[1], b)
        assert set(lines[up]) == {-p, q} and set(lines[down]) == {p, -q}
        equalities[p] = up, down
    final_up = equalities[p][0]
    unit = res(apos, final_up, p)
    empty = res(unit, bneg, q)
    assert lines[empty] == ()
    return {'n': n, 'gates': [list(gate) for gate in gates],
            'variables': n + 5*g, 'axioms': [list(x) for x in axioms],
            'steps': steps}


def examples():
    concrete = [
        ('and', 2, [('AND', 1, 2)]),
        ('or', 2, [('OR', 1, 2)]),
        ('and_or', 3, [('AND', 1, 2), ('OR', 4, 3)]),
        ('or_and', 3, [('OR', 1, 2), ('AND', 4, 3)]),
        ('fanout', 4, [('AND', 1, 2), ('OR', 5, 3), ('AND', 5, 4), ('OR', 6, 7)]),
        ('mixed', 4, [('OR', 1, 2), ('AND', 3, 4), ('OR', 5, 6),
                      ('AND', 7, 1), ('OR', 7, 8)]),
    ]
    for seed in (31, 37, 41, 43, 47):
        rng = random.Random(seed)
        n = 4
        gs = []
        for i in range(10):
            a, b = rng.sample(range(1, n + i + 1), 2)
            gs.append((rng.choice(('AND', 'OR')), a, b))
        concrete.append((f'seed_{seed}', n, gs))
    return concrete


def summarize(proof):
    blob = json.dumps(proof, sort_keys=True, separators=(',', ':')).encode('utf-8')
    n, gates = proof['n'], proof['gates']
    num = len(gates)
    a = sum(op == 'AND' for op, *_ in gates)
    o = num-a
    return {'inputs': n, 'gates': num, 'and_gates': a, 'or_gates': o,
            'variables': proof['variables'], 'source_clauses': len(proof['axioms']),
            'derived_lines': len(proof['steps']), 'upper_bound': 15*a+14*o+2,
            'certificate_sha256': hashlib.sha256(blob).hexdigest()}


def report():
    cases = []
    for name, n, gates in examples():
        row = summarize(certificate(n, gates))
        row['name'] = name
        cases.append(row)
    return {'date': '2026-11-11', 'hypothesis': 'bounded asymmetric monotone De Morgan miter',
            'all_checks_passed': all(c['derived_lines'] <= c['upper_bound'] for c in cases),
            'cases': cases, 'mathematical_scope': 'all admissible AND/OR DAGs',
            'new_lean_theorems': 0, 'p_vs_np_proved': False}


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, default=None)
    args = parser.parse_args()
    data = report()
    content = json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + '\n'
    if args.out:
        args.out.write_text(content, encoding='utf-8')
    else:
        print(content, end='')
