#!/usr/bin/env python3
"""Exhaustively audit monochromatic affine flats of binary inner product.

Explicit cutoff: m in {1,2,3}; the proof for all m is mathematical, not
inferred from this enumeration. The raw affine flats are enumerated by unique
reduced-row-echelon direction bases and all of their cosets.

Run: python experiments/exact_affine_one_cover.py
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, product
import json


def parity(v: int) -> int:
    return v.bit_count() & 1


def q(m: int, z: int) -> int:
    mask = (1 << m) - 1
    return parity((z & mask) & (z >> m))


def subspace_vectors(basis: tuple[int, ...]) -> frozenset[int]:
    vectors = {0}
    for row in basis:
        vectors |= {v ^ row for v in tuple(vectors)}
    return frozenset(vectors)


def all_rref_bases(n: int, d: int):
    """Enumerate every d-plane through zero exactly once, no GL duplication."""
    for pivots in combinations(range(n), d):
        free = [tuple(k for k in range(p + 1, n) if k not in pivots)
                for p in pivots]
        choices = [tuple(1 << p | sum((1 << k) for k, b in zip(row_free, bits) if b)
                         for bits in product((0, 1), repeat=len(row_free)))
                   for p, row_free in zip(pivots, free)]
        for basis in product(*choices):
            yield basis


def audit(m: int) -> dict:
    if not 1 <= m <= 3:
        raise ValueError("Fixed exhaustive budget: 1 <= m <= 3. Do not silently increase.")
    n = 2 * m
    positive = frozenset(z for z in range(1 << n) if q(m, z))
    flats_count = Counter()
    positive_flats = Counter()
    subspaces_count = Counter()
    example_max_flat = None
    for d in range(n + 1):
        for basis in all_rref_bases(n, d):
            subspaces_count[d] += 1
            direction = subspace_vectors(basis)
            assert len(direction) == 1 << d
            seen = set()
            for a in range(1 << n):
                if a in seen:
                    continue
                coset = {a ^ u for u in direction}
                assert not seen.intersection(coset)
                seen.update(coset)
                flats_count[d] += 1
                if coset <= positive:
                    positive_flats[d] += 1
                    if d == m - 1 and example_max_flat is None:
                        example_max_flat = sorted(coset)
            assert len(seen) == 1 << n
    assert len(positive) == (2**m - 1) * 2**(m-1)
    assert not any(positive_flats[d] for d in range(m, n + 1))
    assert positive_flats[m - 1] > 0

    # Explicit disjoint cover: fix nonzero x, solve x·y=1.
    charts = [{x | (y << m) for y in range(1 << m) if parity(x & y)}
              for x in range(1, 1 << m)]
    assert len(charts) == (1 << m) - 1
    assert all(len(s) == 1 << (m - 1) and s <= positive for s in charts)
    assert sum(map(len, charts)) == len(set().union(*charts)) == len(positive)
    assert set().union(*charts) == positive
    return {
        "m": m, "ambient_bits": n, "positive_points": len(positive),
        "subspaces_by_dim": dict(sorted(subspaces_count.items())),
        "cosets_by_dim": dict(sorted(flats_count.items())),
        "positive_cosets_by_dim": dict(sorted(positive_flats.items())),
        "largest_positive_flat_dim": max(positive_flats),
        "exact_minimum_cover_from_proved_size_bound": (1 << m) - 1,
        "explicit_partition_charts": len(charts),
        "max_positive_flat_example": example_max_flat,
    }


def main():
    print(json.dumps({"method": "RREF exhaustive all affine cosets; independent source-count and partition checks",
                      "scope": "finite tests only, m<=3; theorem for all m proven in accompanying note",
                      "results": [audit(m) for m in (1, 2, 3)]},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
