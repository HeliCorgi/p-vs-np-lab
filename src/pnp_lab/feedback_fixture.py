"""One-way binary shields for proper 3-CNF; fixture data are never solver hints.

The last literal of each ordered clause is the default shield endpoint.
With all_sockets=True every literal gets a private strip. SAT projection is
exact in both cases; extending a satisfying word need not be unique.
"""
from itertools import combinations

from .ternary_flow import divergence, onehot_flow, prism_edges

LAYERS = 16


def cubic_tseitin(edges, charges):
    """Encode one parity per vertex of a finite simple cubic graph.

    Return (edge variables, ordered ternary clauses); only the rotation of
    each OR's literals differs from the lab's pre-existing binary-flow CNF.
    """
    ed = tuple(tuple(e) for e in edges)
    q = tuple(charges)
    if not q or any(type(b) is not int or b not in (0, 1) for b in q):
        raise ValueError('invalid charges')
    count = [0] * len(q)
    seen = set()
    for e in ed:
        if (len(e) != 2 or any(type(v) is not int or not 0 <= v < len(q) for v in e)
                or e[0] == e[1] or tuple(sorted(e)) in seen):
            raise ValueError('not a simple graph')
        seen.add(tuple(sorted(e)))
        for v in e:
            count[v] += 1
    if any(x != 3 for x in count):
        raise ValueError('every vertex must have degree three')
    n, rows = onehot_flow(ed, q, modulus=2)
    assert len(rows) == 4 * len(q)
    rotated = []
    for i, row in enumerate(rows):
        # Among each vertex's four clauses omit the coordinate positions
        # 0,1,2,0 from the *start* ternary. Thus all three edge variables are
        # visible in at least two ternaries, including across any sign change.
        j = (i % 4) % 3
        rotated.append(row[:j] + row[j+1:] + (row[j],))
    return n, tuple(rotated)


def shield_clauses(n, clauses, *, layers=LAYERS, word=None, all_sockets=False):
    """Replace literal c by z, with a private directed strip ensuring z -> c.

    Strip variables are start z and two vertices in each of L layers.
    Consecutive internal layers use all four directed implications. For
    L>=2 no strip variable has exactly one positive AND one negative use.
    """
    if type(n) is not int or n < 0 or type(layers) is not int or layers < 1:
        raise ValueError('invalid variable bound or layer count')
    if type(all_sockets) is not bool:
        raise ValueError('invalid socket mode')
    if word is not None and (type(word) is not int or word < 0 or word.bit_length() > n):
        raise ValueError('invalid source word')
    N = n
    lifted = word
    raw = []
    for clause in clauses:
        c = tuple(clause)
        if (len(c) != 3 or any(type(l) is not int or not 1 <= abs(l) <= n for l in c)
                or len({abs(l) for l in c}) != 3):
            raise ValueError('expected a proper ternary clause')
        if word is not None and not any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c):
            raise ValueError('source word falsifies a clause')
        head = [] if all_sockets else list(c[:-1])
        links = []
        for target in (c if all_sockets else c[-1:]):
            z = N + 1
            N += 1 + 2 * layers
            head.append(z)
            prev = (z,)
            for t in range(layers):
                here = (z + 1 + 2*t, z + 2 + 2*t)
                links.extend((-a, b) for a in prev for b in here)
                prev = here
            links.extend((-a, target) for a in prev)
            if word is not None and bool(word >> (abs(target)-1) & 1) == (target > 0):
                lifted |= ((1 << (1 + 2 * layers)) - 1) << (z - 1)
        raw.append(tuple(head))
        raw.extend(links)
    return N, tuple(raw), lifted


def feedback_case(vertices, bad, *, layers=LAYERS, all_sockets=False):
    """Small graph controls; no expansion claim for these K4/prism samples."""
    if type(vertices) is not int or vertices < 4 or vertices % 2 or type(bad) is not bool:
        raise ValueError('vertices must be even and at least four; bad must be Boolean')
    edges = tuple(combinations(range(4), 2)) if vertices == 4 else prism_edges(vertices // 2)
    values = tuple((i+1) % 2 for i in range(len(edges)))
    charge = list(divergence(edges, values, vertices, 2))
    if bad:
        charge[0] ^= 1
    n, core = cubic_tseitin(edges, charge)
    word = None if bad else sum(x << i for i, x in enumerate(values))
    N, raw, lifted = shield_clauses(n, core, layers=layers, word=word, all_sockets=all_sockets)
    return N, raw, lifted, core
