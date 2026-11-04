"""Positive and adversarial tagged XOR families for decision-pruning labels.

Variable IDs for controls: tags 1..k; y_i=k+i+1; z_i=2k+i+1.
All controls use raw signed width-three CNF. See docs/codec_controls.md.
"""
from itertools import product


def _xor_triple(a, b, c):
    """Forbid exactly the four assignments with odd a XOR b XOR c."""
    for bits in product((0, 1), repeat=3):
        if sum(bits) % 2 == 1:
            yield tuple((-v if s else v) for v, s in zip((a, b, c), bits))


def tagged_xor(k, core=(), *, marked=False):
    """Encode t_i=y_i XOR z_i and a proper nonlinear CNF on logical y IDs 1..k.

    marked=True also forces each y_i and z_i to occur in an exactly-one block
    with two private auxiliary variables. All y,z assignments still extend.
    """
    if type(k) is not int or k < 1 or type(marked) is not bool:
        raise ValueError("k must be a positive integer and marked must be Boolean")
    cs = []
    for row in core:
        row = tuple(row)
        if not 2 <= len(row) <= 3 or any(type(l) is not int or not (1 <= abs(l) <= k) for l in row):
            raise ValueError("core must use proper clauses of width 2 or 3 on the y coordinates")
        if len(set(abs(l) for l in row)) != len(row):
            raise ValueError("repeated core variable")
        cs.append(tuple((k+abs(l)) * (1 if l > 0 else -1) for l in row))
    for i in range(k):
        cs.extend(_xor_triple(i+1, k+i+1, 2*k+i+1))
    n = 3*k
    if marked:
        for v in range(k+1, 3*k+1):
            a, b = n+1, n+2
            n += 2
            cs.extend(((v, a, b), (-v, -a), (-v, -b), (-a, -b)))
    return n, tuple(cs)


def prefix_restriction(clauses, d, mask):
    """Set original IDs 1..d, keeping all other IDs unchanged (no renaming)."""
    if type(d) is not int or d < 0 or type(mask) is not int or not 0 <= mask < (1 << d):
        raise ValueError("invalid prefix")
    out = []
    for cl in clauses:
        if any(abs(v) <= d and bool(mask & (1 << (abs(v)-1))) == (v > 0) for v in cl):
            continue
        out.append(tuple(v for v in cl if abs(v) > d))
    return tuple(out)


def coupled_core(k):
    """Nonlinear example with overlapping triples; all-true is a solution."""
    if type(k) is not int or k < 3:
        raise ValueError("at least three tag positions required")
    return tuple((i+1, (i+1) % k+1, (i+2) % k+1) for i in range(k))


def marked_model(k, tag):
    """One raw witness for the marked positive cyclic core at the given tag word."""
    if type(k) is not int or k < 1 or type(tag) is not int or not 0 <= tag < (1 << k):
        raise ValueError("invalid tag")
    # t=tag, y=all ones, z=tag XOR y. In each marker choose its first
    # private bit iff the core bit is zero, and never select its second.
    ones = (1 << k)-1
    w = tag | (ones << k) | ((ones ^ tag) << (2*k))
    for i in range(2*k):
        if not bool(w & (1 << (k+i))):
            w |= 1 << (3*k+2*i)
    return w
