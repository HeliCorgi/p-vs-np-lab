"""Discover an integer obstruction by canceling all but one column.

Generate ordinary integer_hull certificates. The projected clauses, and no
gate, chosen modulus, graph, signs, or ordering hints, are input. Failure only
means this restricted certificate search did not succeed.
"""
from collections import defaultdict, deque
from itertools import product

from .integer_hull import KIND, MAX_BITS, check_integer_hull
from .modular_hull import _input


def one_column_certificate(n, projected_clauses, *, max_bits=MAX_BITS):
    """Find unit-weight signed sums of exact three-variable table laws."""
    if type(max_bits) is not int or not 0 <= max_bits <= MAX_BITS:
        raise ValueError('invalid integer bit limit')
    cs = _input(n, projected_clauses)
    groups = defaultdict(dict)
    for i, c in enumerate(cs):
        s = tuple(sorted(map(abs, c)))
        if len(s) != 3 or len(set(s)) != 3:
            continue
        bad = sum((1 << j) for j, v in enumerate(s) if -v in c)
        groups[s].setdefault(bad, i)
    stats = dict(triples=len(groups), table_cells=0, unit_normal_tests=0,
                 exact_rows=0, incidence_visits=0, heavy_columns=0,
                 max_accumulator_bits=0, budget_limited=False)
    rows = []
    incidence = defaultdict(list)
    for scope, excluded in sorted(groups.items()):
        stats['table_cells'] += 8
        allowed = [w for w in range(8) if w not in excluded]
        if len(allowed) != 3:
            continue
        for tail in product((-1, 1), repeat=2):
            a = (1,) + tail
            stats['unit_normal_tests'] += 1
            values = {sum(c for j, c in enumerate(a) if w >> j & 1) for w in allowed}
            if len(values) == 1:
                b, = values
                i = len(rows)
                rows.append(dict(scope=list(scope), clauses=sorted(excluded.values()),
                                 coeff=list(a), rhs=b, modulus=0))
                for v, c in zip(scope, a):
                    incidence[v].append((i, c))
                break
    stats['exact_rows'] = len(rows)
    heavy = [v for v, occ in incidence.items() if len(occ) > 2]
    stats['heavy_columns'] = len(heavy)
    if len(heavy) != 1 or any(len(occ) == 1 for occ in incidence.values()):
        return None, stats
    h, = heavy
    adj = [[] for _ in rows]
    for v, occ in incidence.items():
        if v != h:
            (i, a), (j, b) = occ
            sign = -a*b
            adj[i].append((j, sign))
            adj[j].append((i, sign))
    weights = [0]*len(rows)
    for i in range(len(rows)):
        if weights[i]:
            continue
        weights[i] = 1
        queue = deque([i])
        while queue:
            u = queue.popleft()
            for v, sign in adj[u]:
                stats['incidence_visits'] += 1
                need = sign*weights[u]
                if not weights[v]:
                    weights[v] = need
                    queue.append(v)
                elif weights[v] != need:
                    return None, stats
    charge = coef = 0
    for w, row in zip(weights, rows):
        charge += w*row['rhs']
        coef += w*next((a for v, a in zip(row['scope'], row['coeff']) if v == h), 0)
        stats['max_accumulator_bits'] = max(stats['max_accumulator_bits'],
                                            abs(coef).bit_length(), abs(charge).bit_length())
        if stats['max_accumulator_bits'] > max_bits or abs(row['rhs']).bit_length() > max_bits:
            stats['budget_limited'] = True
            return None, stats
    modulus = abs(coef)
    if modulus <= 1 or charge % modulus == 0:
        return None, stats
    cert = dict(kind=KIND, modulus=modulus, residual_rhs=charge % modulus,
                terms=[dict(row, weight=w) for row, w in zip(rows, weights)])
    if not check_integer_hull(n, cs, cert):
        raise AssertionError('one-column proposal failed raw table and weighted-sum replay')
    stats.update(modulus=modulus, residual_rhs=cert['residual_rhs'], certificate_terms=len(rows))
    return cert, stats
