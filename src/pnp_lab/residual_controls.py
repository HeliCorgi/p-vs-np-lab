"""Explicit width-three CNFs separating decision labels from exact/modular counts.

Literal IDs start at one. On a fixed-t residual, count assignments to exactly
the remaining declared coordinates, including the (uniquely determined) gates.
Large-instance formulas below are mathematical predictions, not enumeration.
"""


def _integer(x, lower, upper=None):
    if type(x) is not int or x < lower or (upper is not None and x > upper):
        raise ValueError("argument is outside its integer domain")
    return x


def comparator_cnf(k):
    """Return signed clauses for the k-bit comparison u <= t on 3k bits.

    Increasing bit significance is used within t,u,q, in that order. The
    output q[-1] of the final gate is constrained true; the initial carry
    is the constant true (not another free or counted variable).
    """
    _integer(k, 1)
    clauses = []
    for i in range(k):
        a, b, y = i+1, -(k+i+1), 2*k+i+1
        if i == 0:  # maj(a,b,1) = a OR b
            clauses.extend([(-a, y), (-b, y), (a, b, -y)])
        else:
            c = y-1
            for p, q in ((a, b), (a, c), (b, c)):
                clauses.extend([(-p, -q, y), (p, q, -y)])
    return tuple(clauses+[(3*k,)])


def residual_cnf(k, depth, prefix):
    """H_prefix: set the depth high t bits and compact the remaining scope.

    Return (variable_count, clauses), even when some variables don't occur.
    Variable order: free low t bits, all u bits, all q bits. In particular
    two residuals of the same k and depth have the same labelled scope.
    """
    _integer(k, 1)
    _integer(depth, 0, k)
    _integer(prefix, 0, (1 << depth)-1)
    r = k-depth
    out = []
    for clause in comparator_cnf(k):
        kept = []
        for lit in clause:
            v = abs(lit)
            if r < v <= k:
                val = bool(prefix & (1 << (v-1-r)))
                if val == (lit > 0):
                    break
            else:
                w = v if v <= r else v-depth
                kept.append(w if lit > 0 else -w)
        else:
            out.append(tuple(kept))
    return 3*k-depth, tuple(out)


def satisfies(clauses, word):
    """Evaluate a signed CNF directly, including units and empty clauses."""
    return all(any(bool(word & (1 << (abs(lit)-1))) == (lit > 0)
                   for lit in clause) for clause in clauses)


def predicted_residual_count(k, depth, prefix):
    """Sum (t+1) over suffixes; no counting oracle or simulation."""
    _integer(k, 1)
    _integer(depth, 0, k)
    _integer(prefix, 0, (1 << depth)-1)
    width = 1 << (k-depth)
    return prefix*width*width + width*(width+1)//2


def modular_collision(m):
    """Return a common-scope UNSAT anchor, SAT partner, and UNSAT partner.

    The positive partner has exactly m models; the two anchored ORs collide
    modulo m. These residuals can also be embedded at one depth using outer
    selector bits as described in docs/pruning_obstructions.md.
    """
    _integer(m, 1)
    k = max(1, (m-1).bit_length())
    n, positive = residual_cnf(k, k, m-1)
    false = ((1,), (-1,))
    return n, false, positive, false


def majority(a, b, c):
    """Coordinatewise majority on bitmasks."""
    return (a & b) | (a & c) | (b & c)
