#!/usr/bin/env python3
"""Tseitin AND/XOR lift of binary inner product: bounded independent audit.

No SAT solving oracle, no extended-ambient affine-flat enumeration.
Enumerate all extended assignments only for m=1..3; general conclusions
are proved separately by the mathematical projection/lift argument.
"""
from __future__ import annotations

from itertools import combinations
import json


def eval_clause(clause: tuple[int, ...], assignment: int) -> bool:
    """DIMACS one-based signed literals, independent literal truth evaluation."""
    return any(bool((assignment >> (abs(lit) - 1)) & 1) == (lit > 0) for lit in clause)


def build_cnf(m: int) -> tuple[int, tuple[tuple[int, ...], ...], tuple[int, ...]]:
    if m < 1:
        raise ValueError('m >= 1')
    # DIMACS variables: x_0..x_{m-1}; y_0..; p_0..; t_1..
    x = tuple(i+1 for i in range(m))
    y = tuple(m+i+1 for i in range(m))
    p = tuple(2*m+i+1 for i in range(m))
    t = tuple(3*m+i for i in range(1,m))
    clauses = []
    for i in range(m):
        # p_i iff x_i AND y_i
        clauses.extend([(-p[i],x[i]),(-p[i],y[i]),(p[i],-x[i],-y[i])])
    last = p[0]
    for i in range(1,m):
        out = t[i-1]
        # out iff (last XOR p_i)
        clauses.extend([(last,p[i],-out),(last,-p[i],out),
                        (-last,p[i],out),(-last,-p[i],-out)])
        last = out
    clauses.append((last,))
    size = 4*m - 1
    assert max(abs(lit) for clause in clauses for lit in clause) == size
    assert len(clauses) == 7*m-3
    assert all(1 <= len(clause) <= 3 for clause in clauses)
    return size, tuple(clauses), t


def extension(m: int, z: int) -> int:
    """Unique gate assignment for original bits x|y (bit order: x, y)."""
    mask = (1 << m)-1
    x, y = z & mask, (z >> m) & mask
    out = z
    acc = 0
    for i in range(m):
        bit = ((x>>i)&1) & ((y>>i)&1)
        out |= bit << (2*m+i)
        acc ^= bit
        if i > 0:
            out |= acc << (3*m+i-1)
    return out


def positive(m: int, z: int) -> bool:
    mask = (1 << m)-1
    return (((z & mask) & (z >> m)).bit_count() & 1) == 1


def verify(m: int) -> dict:
    if not 1 <= m <= 3:
        raise ValueError('fixed independent finite audit budget: 1 <= m <= 3')
    n, cnf, _ = build_cnf(m)
    # Independent full evaluator, does NOT build a gate assignment.
    sat_assignments = {assignment for assignment in range(1 << n)
                       if all(eval_clause(clause, assignment) for clause in cnf)}
    expected = {extension(m,z) for z in range(1<<(2*m)) if positive(m,z)}
    assert sat_assignments == expected
    assert len(expected) == (2**m-1)*2**(m-1)
    assert len({a & ((1<<(2*m))-1) for a in expected}) == len(expected)
    assert all(not all(eval_clause(clause, extension(m,z)) for clause in cnf)
               for z in range(1 << (2*m)) if not positive(m,z))
    # The explicit upper cover: x is nonzero and fixed, y ranges over x.y=1.
    charts = []
    for x in range(1,1<<m):
        lifted = {extension(m, x | (y<<m)) for y in range(1<<m)
                  if ((x & y).bit_count() & 1)}
        anchor = next(iter(lifted))
        directions = {w ^ anchor for w in lifted}
        assert len(lifted) == 1<<(m-1)
        assert all((u ^ v) in directions for u in directions for v in directions)
        charts.append(lifted)
    assert set().union(*charts) == expected
    assert sum(map(len,charts)) == len(expected)
    # Independent small-plane enumerator, not the earlier phase-25 RREF search.
    # Every affine 2-flat consists of four distinct elements whose xor is 0.
    # A 1-flat is any pair; a 0-flat is any singleton.
    original_pos = {z for z in range(1 << (2*m)) if positive(m,z)}
    original_flats_by_dim = {0: len(original_pos)}
    lifted_flats_by_dim = {0: len(original_pos)}
    if len(original_pos) >= 2:
        pairs = list(combinations(sorted(original_pos),2))
        original_flats_by_dim[1] = len(pairs)
        lifted_flats_by_dim[1] = len(pairs)
    if m >= 3:
        planes = [f for f in combinations(sorted(original_pos),4)
                  if f[0]^f[1]^f[2]^f[3] == 0]
        original_flats_by_dim[2] = len(planes)
        lifted_flats_by_dim[2] = sum(1 for f in planes
            if extension(m,f[0]) ^ extension(m,f[1]) ^
               extension(m,f[2]) ^ extension(m,f[3]) == 0)
    positive_flats = sum(original_flats_by_dim.values())
    lifted_affine_flats = sum(lifted_flats_by_dim.values())
    assert lifted_affine_flats >= (2**m-1)
    return {'m':m,'variables':n,'clauses':len(cnf),'max_clause_width':3,
            'original_positive_assignments':len(expected),
            'cnf_satisfying_assignments':len(sat_assignments),
            'explicit_affine_cover':len(charts),
            'original_positive_flats':positive_flats,
            'original_flats_by_dim':original_flats_by_dim,
            'affine_flats_after_tseitin_lift':lifted_affine_flats,
            'lifted_flats_by_dim':lifted_flats_by_dim}


def main():
    print(json.dumps({'scope':'finite tests only, fixed m=1..3',
                      'theorem':'exact cover 2^m-1 follows from mathematical projection and affine fibers',
                      'results':[verify(m) for m in (1,2,3)]},indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
