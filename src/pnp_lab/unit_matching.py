"""Decide XOR choice when every option is zero or a unit mask, by perfect matching.

Each group selects one port. Per-coordinate cliques can pair all the leftover
ports iff the desired selection parity holds. A separate dummy coordinate counts
zero choices and does not restrict any originally legal solution.

The graph solver is a deterministic, unweighted Edmonds augmenting-tree /
odd-blossom algorithm, written with only stdlib. Reference: Jack Edmonds,
"Paths, Trees, and Flowers", Canadian J. Math. 17 (1965), 449–467,
https://doi.org/10.4153/CJM-1965-045-4 . Implementation tests are not a
formal verification of that algorithm or a per-instance optimality certificate.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from functools import reduce
from itertools import combinations
from operator import xor


@dataclass(frozen=True)
class UnitMatchingInstance:
    supports: tuple[tuple[int, ...], ...]
    rhs: int
    neighbors: tuple[tuple[int, ...], ...]
    # Group vertices, then option ports, then at most one pad per row.
    port_value: tuple[int | None, ...]
    # A bucket contains all ports of one option value and its optional pad.
    buckets: tuple[tuple[int, ...], ...]
    option_count: int
    pad_count: int
    dummy_parity: int


def reduce_unit_supports(supports, rhs: int) -> UnitMatchingInstance:
    """Make an explicit simple ordinary graph, including required absent rows."""
    if type(rhs) is not int or rhs < 0:
        raise ValueError("rhs must be a nonnegative integer")
    groups = []
    try:
        if isinstance(supports, (str, bytes)):
            raise ValueError("expected finite supports")
        for raw in supports:
            if isinstance(raw, (str, bytes)):
                raise ValueError("expected a finite support")
            values = set()
            for mask in raw:
                if type(mask) is not int or mask < 0 or mask.bit_count() > 1:
                    raise ValueError("each option must be zero or a nonnegative unit mask")
                values.add(mask)
            groups.append(tuple(sorted(values)))
    except TypeError as exc:
        raise ValueError("expected an iterable of finite supports") from exc

    g = len(groups)
    adj = [[] for _ in groups]
    label: list[int | None] = [None] * g
    bucket: dict[int, list[int]] = {0: []}

    def vertex(value=None):
        label.append(value)
        adj.append([])
        return len(adj)-1

    def edge(i, j):
        adj[i].append(j)
        adj[j].append(i)

    for i, group in enumerate(groups):
        for option in group:
            v = vertex(option)
            edge(i, v)
            bucket.setdefault(option, []).append(v)

    # Missing requested bits get singleton cliques (isolated pad vertices).
    # Iterate over present bits, so a sparse high-bit mask is not an array index.
    remaining = rhs
    while remaining:
        bit = remaining & -remaining
        bucket.setdefault(bit, [])
        remaining ^= bit
    dummy = (g ^ rhs.bit_count()) & 1
    pads = 0
    opts = len(adj)-g
    for key, ports in sorted(bucket.items()):
        required = dummy if key == 0 else int(bool(rhs & key))
        if (len(ports) & 1) != required:
            ports.append(vertex())
            pads += 1
        for u, v in combinations(ports, 2):
            edge(u, v)
    return UnitMatchingInstance(tuple(groups), rhs, tuple(tuple(sorted(a)) for a in adj),
                                tuple(label), tuple(tuple(bucket[k]) for k in sorted(bucket)),
                                opts, pads, dummy)


def _check_matching(adj, mate, *, perfect=False):
    n = len(adj)
    if len(mate) != n:
        raise ValueError("matching has wrong length")
    for v, w in enumerate(mate):
        if type(w) is not int:
            raise ValueError("matching vertices must be integers")
        if w == -1 and not perfect:
            continue
        if not 0 <= w < n or w not in adj[v] or mate[w] != v:
            raise ValueError("not a valid matching")


def lift_unit_choices(instance: UnitMatchingInstance, choices) -> tuple[int, ...]:
    """Construct a perfect matching from one satisfying choice per source group."""
    choices = tuple(choices)
    if (len(choices) != len(instance.supports) or
            any(type(x) is not int or x not in group for x, group in zip(choices, instance.supports))
            or reduce(xor, choices, 0) != instance.rhs):
        raise ValueError("choices do not satisfy the unit-support instance")
    mate = [-1] * len(instance.neighbors)
    for i, x in enumerate(choices):
        v = next(v for v in instance.neighbors[i] if instance.port_value[v] == x)
        mate[i], mate[v] = v, i
    for bucket in instance.buckets:
        unused = [v for v in bucket if mate[v] == -1]
        if len(unused) % 2:
            raise AssertionError("invalid bucket parity in witness lift")
        for j in range(0, len(unused), 2):
            u, v = unused[j:j+2]
            mate[u], mate[v] = v, u
    _check_matching(instance.neighbors, mate, perfect=True)
    return tuple(mate)


def project_unit_matching(instance: UnitMatchingInstance, mate) -> tuple[int, ...]:
    """Validate the perfect matching and independently check the projected XOR."""
    _check_matching(instance.neighbors, mate, perfect=True)
    choices = tuple(instance.port_value[mate[i]] for i in range(len(instance.supports)))
    if (any(x is None or x not in group for x, group in zip(choices, instance.supports))
            or reduce(xor, choices, 0) != instance.rhs):
        raise AssertionError("matching failed original support check")
    return choices


def maximum_matching(neighbors) -> dict:
    """Maximum-cardinality matching of a finite simple undirected graph.

    One rooted alternating-tree search scans each outer vertex once. Its bases
    encode contracted odd blossoms; predecessor rewrites retain how to lift an
    augmenting path to original vertices. We restart after each augmentation,
    trying all exposed roots before declaring no path exists. With V vertices
    and E edges this conservative version uses O(V²(E+V²)) elementary operations
    (plus input normalization); every contraction strictly reduces the number
    of distinct bases, and each contraction takes O(V) operations.
    """
    raw = list(neighbors)
    n = len(raw)
    adj_sets = []
    for v, entries in enumerate(raw):
        row = set()
        for w in entries:
            if type(w) is not int or not 0 <= w < n or w == v:
                raise ValueError("graph must be simple with indexed vertices")
            row.add(w)
        adj_sets.append(row)
    if any(v not in adj_sets[w] for v, row in enumerate(adj_sets) for w in row):
        raise ValueError("graph must be undirected")
    adj = [tuple(sorted(row)) for row in adj_sets]
    mate = [-1] * n
    metrics = dict(searches=0, augmentations=0, blossom_contractions=0, scanned_adjacencies=0)

    def augment_from(root):
        metrics["searches"] += 1
        pred = [-1] * n  # parent across a nonmatching edge; rewritten on contraction
        base = list(range(n))
        outer = [False] * n
        outer[root] = True
        queue = deque([root])

        def up(b):
            # b is an outer base other than root. Its mate is inner and has a parent.
            if mate[b] < 0 or pred[mate[b]] < 0:
                raise AssertionError("broken alternating-tree ancestry")
            return base[pred[mate[b]]]

        def contract(u, v):
            # An edge between distinct outer bases closes an odd cycle. Locate
            # the common ancestor in the contracted alternating tree.
            ancestors = [False] * n
            b = base[u]
            while not ancestors[b]:
                ancestors[b] = True
                if b == root:
                    break
                b = up(b)
            common = base[v]
            while not ancestors[common]:
                common = up(common)
            blossom = [False] * n

            def trace_arm(start, child):
                p = start
                while base[p] != common:
                    m = mate[p]
                    if m < 0 or pred[m] < 0:
                        raise AssertionError("broken blossom arm")
                    blossom[base[p]] = blossom[base[m]] = True
                    parent = pred[m]
                    pred[p] = child
                    child, p = m, parent
            trace_arm(u, v)
            trace_arm(v, u)
            for p in range(n):
                if blossom[base[p]]:
                    base[p] = common
                    if not outer[p]:
                        outer[p] = True
                        queue.append(p)
            metrics["blossom_contractions"] += 1

        while queue:
            u = queue.popleft()
            for v in adj[u]:
                metrics["scanned_adjacencies"] += 1
                if base[u] == base[v] or mate[u] == v:
                    continue
                if outer[v]:
                    contract(u, v)
                elif pred[v] < 0:
                    # First route to this inner endpoint. If exposed, the tree
                    # contains an augmenting path; otherwise label its mate outer.
                    pred[v] = u
                    if mate[v] < 0:
                        end = v
                        while end >= 0:
                            p = pred[end]
                            if p < 0:
                                raise AssertionError("missing augmentation predecessor")
                            next_end = mate[p]
                            mate[end], mate[p] = p, end
                            end = next_end
                        return True
                    outer[mate[v]] = True
                    queue.append(mate[v])
        return False

    while True:
        if not any(augment_from(v) for v in range(n) if mate[v] < 0):
            break
        metrics["augmentations"] += 1
    _check_matching(adj_sets, mate)
    size = sum(w >= 0 for w in mate) // 2
    if size != metrics["augmentations"]:
        raise AssertionError("augmentation count mismatch")
    return dict(mate=mate, size=size, **metrics)


def decide_unit_supports(supports, rhs: int) -> dict:
    """Return SAT/UNSAT, a checked choice witness on SAT, and actual graph/work counters."""
    instance = reduce_unit_supports(supports, rhs)
    answer = maximum_matching(instance.neighbors)
    mate = answer.pop("mate")
    size = answer.pop("size")
    sat = 2*size == len(mate)
    witness = list(project_unit_matching(instance, mate)) if sat else None
    return {"status": "SAT" if sat else "UNSAT", "witness": witness,
            "groups": len(instance.supports), "distinct_options": instance.option_count,
            "padding_vertices": instance.pad_count, "dummy_parity": instance.dummy_parity,
            "graph_vertices": len(mate), "graph_edges": sum(map(len, instance.neighbors))//2,
            "matching_edges": size, **answer}
