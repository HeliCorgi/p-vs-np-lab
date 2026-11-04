"""Polynomial, one-way sound labels for existential CNF decision on a named scope.

Matching labels imply equal satisfiability. Different labels need not indicate
different answers. No sparsity theorem for unrestricted inputs.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations


def canonical_cnf(n, cnf, max_clause_width=6):
    if type(n) is not int or n < 0 or type(max_clause_width) is not int or max_clause_width < 0:
        raise ValueError('Invalid scope or width.')
    incoming = set()
    for clause in cnf:
        raw = tuple(clause)
        if len(raw) > max_clause_width or any(type(l) is not int or not 1 <= abs(l) <= n for l in raw):
            raise ValueError('Clause outside the stated scope or width.')
        row = frozenset(raw)
        if any(-l in row for l in row):
            continue
        incoming.add(tuple(sorted(row, key=abs)))
    if () in incoming:
        return ((),)
    # With width at most six, at most 63 strict subsets per clause.
    return tuple(sorted(c for c in incoming if not any(
        sub in incoming for j in range(1, len(c)) for sub in combinations(c, j))))


def or_cnf(n, left, right):
    """A same-variable OR of two width-three CNFs, logically equivalent pointwise."""
    a = canonical_cnf(n, left, 3)
    b = canonical_cnf(n, right, 3)
    return canonical_cnf(n, (p+q for p in a for q in b))


def _project_equations(rows, shared):
    # Pivot on private columns before reducing the shared subsystem.
    # At private pivot p, only lower private coordinates can be needed for lifting.
    private, core = {}, {}
    for mask, rhs in rows:
        while mask & ~shared:
            p = (mask & ~shared).bit_length()-1
            if p not in private:
                private[p] = mask, rhs
                break
            a, b = private[p]
            mask, rhs = mask ^ a, rhs ^ b
        else:
            while mask:
                p = mask.bit_length()-1
                if p not in core:
                    core[p] = mask, rhs
                    break
                a, b = core[p]
                mask, rhs = mask ^ a, rhs ^ b
            else:
                if rhs:
                    return None
    for i in sorted(core):
        mask, rhs = core[i]
        for p in core:
            if p > i and core[p][0] >> i & 1:
                a, b = core[p]
                core[p] = a ^ mask, b ^ rhs
    return tuple(core[p] for p in sorted(core))


def blocked_normal_form(clauses):
    """Fixed point of blocked-clause elimination on a canonical CNF.

    Remove a clause if it can be repaired by flipping one of its literals.
    Simultaneous removals are equivalent to sequential ones: blocking on
    a literal is preserved when other clauses are deleted.
    """
    while clauses:
        indexed = defaultdict(list)
        for row in clauses:
            for l in row:
                indexed[l].append(row)
        keep = []
        for c in clauses:
            complements = {-l for l in c}
            if not any(all(any(j != -lit and j in complements for j in other)
                           for other in indexed[-lit])
                       for lit in c):
                keep.append(c)
        if len(keep) == len(clauses):
            break
        clauses = tuple(keep)
    return clauses


def residual_label(n, cnf, mode='affine'):
    """Include ordered core clauses/rows themselves, not a lossy digest."""
    if mode not in ('syntax', 'affine', 'blocked'):
        raise ValueError('Expected syntax, affine or blocked.')
    clauses = canonical_cnf(n, cnf)
    if mode == 'blocked': clauses = blocked_normal_form(clauses)
    if not clauses: return ('YES',)
    if clauses == ((),): return ('NO',)
    if mode == 'syntax': return ('CNF', clauses)
    groups = defaultdict(lambda: ([], []))
    for c in clauses:
        scope = tuple(map(abs, c))
        groups[scope][sum(l < 0 for l in c) % 2].append(c)
    rows, leftover = [], []
    for scope, classes in groups.items():
        half = 1 << (len(scope)-1)
        full = [b for b in (0, 1) if len(classes[b]) == half]
        if len(full) == 2: return ('NO',)
        if full:
            # Every bad sign pattern of parity b is present, so parity must be 1-b.
            b = full[0]
            rows.append((sum(1 << (j-1) for j in scope), 1-b))
            leftover.extend(classes[1-b])
        else:
            leftover.extend(classes[0])
            leftover.extend(classes[1])
    shared = 0
    for c in leftover:
        for l in c: shared |= 1 << (abs(l)-1)
    projected = _project_equations(rows, shared)
    if projected is None: return ('NO',)
    if not leftover: return ('YES',)
    return ('CORE', tuple(sorted(leftover)), projected)
