"""Certified graphic recoding of a choice of at most three XOR masks per group.

A basis of the within-group differences is mapped to the incidence columns
of a tree. Each other difference must also map to an edge. Checking this
positive certificate is polynomial; automatic discovery here is bounded
search, not a general polynomial graphic-matroid recognition implementation.
Failure to obtain a representation does not imply UNSAT.
"""
from __future__ import annotations

from functools import reduce
from heapq import heapify, heappop, heappush
from itertools import combinations, product
from operator import xor

from .frontier import _read_groups
from .unit_matching import decide_unit_supports


class _Coordinates:
    def __init__(self, vectors):
        self.basis = []
        self.rows = {}
        for v in vectors:
            rest, code = self.decompose(v)
            if rest:
                self.rows[rest.bit_length()-1] = (rest, code ^ (1 << len(self.basis)))
                self.basis.append(v)

    def decompose(self, v):
        code = 0
        while v:
            row = self.rows.get(v.bit_length()-1)
            if row is None:
                break
            v ^= row[0]
            code ^= row[1]
        return v, code


def _setup(supports):
    groups = _read_groups(supports)
    if any(len(g) > 3 for g in groups):
        raise ValueError('graphic support backend requires at most three distinct choices per group')
    diffs = sorted({a ^ b for g in groups for a, b in combinations(g, 2)},
                   key=lambda v: (v.bit_count(), v))
    co = _Coordinates(diffs)
    codes = {0: 0}
    for d in diffs:
        rest, codes[d] = co.decompose(d)
        if rest:
            raise AssertionError('Difference missing from its own basis')
    return groups, co, codes


def graphic_difference_basis(supports):
    """Original bit vectors in the deterministic basis used by certificate APIs."""
    return tuple(_setup(supports)[1].basis)


def _linear(code, columns):
    val = 0
    while code:
        bit = code & -code
        val ^= columns[bit.bit_length()-1]
        code ^= bit
    return val


def _columns(edges):
    return [(1 << a) | (1 << b) for a, b in edges]


def _tree_edges(edges, rank):
    try:
        data = tuple(tuple(e) for e in edges)
    except TypeError as exc:
        raise ValueError('expected one endpoint pair per basis vector') from exc
    if len(data) != rank:
        raise ValueError('wrong number of basis edges')
    parent = list(range(rank+1))

    def find(i):
        while i != parent[i]:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for e in data:
        if (len(e) != 2 or any(type(i) is not int or not 0 <= i <= rank for i in e)):
            raise ValueError('basis edge endpoints must be integers in [0,rank]')
        a, b = map(find, e)
        if a == b:
            raise ValueError('basis edges must form a tree')
        parent[a] = b
    return data  # rank acyclic edges on rank+1 vertices: connected (also for rank zero).


def _valid(codes, edges):
    cols = _columns(edges)
    return all(_linear(v, cols).bit_count() == 2 for d, v in codes.items() if d)


def verify_graphic_certificate(supports, certificate):
    """Check exact basis identity, acyclicity/injectivity and ALL difference images."""
    _, co, codes = _setup(supports)
    if not isinstance(certificate, dict):
        raise ValueError('expected a certificate dictionary')
    given = certificate.get('basis_vectors')
    if (not isinstance(given, (list,tuple)) or any(type(x) is not int for x in given)
            or list(given) != co.basis):
        raise ValueError('basis does not agree with original supports')
    edges = _tree_edges(certificate.get('basis_edges'), len(co.basis))
    if not _valid(codes, edges):
        raise ValueError('a difference is not represented by a single edge')
    return True


def _prufer_tree(code, rank):
    # A vertex-label tree rooted at 0 labels each edge by its child-1.
    # Conversely, label any rooted edge-labelled basis tree this way; hence
    # enumerating all Prüfer sequences covers every edge-labelled topology.
    n = rank + 1
    degree = [1]*n
    for v in code:
        degree[v] += 1
    leaves = [i for i,k in enumerate(degree) if k == 1]
    heapify(leaves)
    adj = [[] for _ in range(n)]
    for p in code:
        v = heappop(leaves)
        adj[v].append(p)
        adj[p].append(v)
        degree[p] -= 1
        if degree[p] == 1:
            heappush(leaves, p)
    a,b = leaves
    adj[a].append(b)
    adj[b].append(a)
    out = [None]*rank
    stack = [(0,-1)]
    while stack:
        u, parent = stack.pop()
        for v in adj[u]:
            if v != parent:
                out[v-1] = (v,u)
                stack.append((v,u))
    return tuple(out)


def _adjacency_tree(codes, rank):
    """Heuristic: reconstruct cliques of forced incident basis-edge pairs.

    If some incidences are missing, the heuristic may fail. Accept only
    after independently checking all difference coordinates on its tree.
    """
    neighbors = [set() for _ in range(rank)]
    for v in codes.values():
        if v.bit_count() == 2:
            a = (v & -v).bit_length()-1
            b = v.bit_length()-1
            neighbors[a].add(b)
            neighbors[b].add(a)
    cliques = set()
    for a, ns in enumerate(neighbors):
        for b in ns:
            if a < b:
                cliques.add(tuple(sorted({a,b} | (ns & neighbors[b]))))
    membership = [[] for _ in range(rank)]
    for k, clique in enumerate(sorted(cliques)):
        for v in clique:
            membership[v].append(k)
            if len(membership[v]) > 2:
                return None
    n = len(cliques)
    for m in membership:
        while len(m) < 2:
            m.append(n)
            n += 1
    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for a,b in membership:
        u,v = find(a),find(b)
        if u == v:
            return None
        parent[u] = v
    # Glue one vertex of each forest component to vertex 0. No new cycle.
    roots = {find(i) for i in range(n)}
    labels = {v:i+1 for i,v in enumerate(v for v in range(n) if v not in roots)}
    return tuple((labels.get(a,0),labels.get(b,0)) for a,b in membership)


def _candidates(codes, rank):
    yield 'star', tuple((0,i+1) for i in range(rank))
    if rank < 3:
        return
    yield 'natural_path', tuple((i,i+1) for i in range(rank))
    tree = _adjacency_tree(codes,rank)
    if tree is not None:
        yield 'forced_adjacencies', tree
    for seq in product(range(rank+1),repeat=rank-1):
        yield 'prufer', _prufer_tree(seq,rank)


def decide_graphic_supports(supports, rhs, *, basis_edges=None, max_tree_trials=256):
    """Exact if a certificate is checked; otherwise may return UNKNOWN.

    basis_edges matches the order from graphic_difference_basis. Its rank r
    pairs must form a tree on vertices 0..r and represent every nonzero
    difference by an edge; a bad supplied certificate raises ValueError. The
    trial budget counts tested trees, not bit operations or matching work.
    An affine-span contradiction is decisive without a tree. Exhaustion of
    all tree topologies establishes only nonrepresentability, never UNSAT.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError('rhs must be a nonnegative mask')
    if type(max_tree_trials) is not int or max_tree_trials < 0:
        raise ValueError('max_tree_trials must be a nonnegative integer')
    groups, co, codes = _setup(supports)
    rank = len(co.basis)
    out = dict(status='UNKNOWN',reason=None,witness=None,rank=rank,differences=len(codes)-1,
               tree_trials=0,max_tree_trials=max_tree_trials,certificate=None,tree_method=None,
               matching=None,matching_calls=0)
    edges = None
    if basis_edges is not None:
        edges = _tree_edges(basis_edges,rank)
        if not _valid(codes,edges):
            raise ValueError('a difference is not represented by a single edge')
        out['tree_method'] = 'supplied'
    if any(not g for g in groups):
        out.update(status='UNSAT',reason='empty_support')
        return out
    target = rhs ^ reduce(xor,(g[0] for g in groups),0)
    rest, target_code = co.decompose(target)
    if rest:
        out.update(status='UNSAT',reason='outside_affine_hull')
        return out
    if edges is None:
        if len(codes)-1 > rank*(rank+1)//2:
            out.update(reason='too_many_distinct_edges')
            return out
        if rank == 0:
            edges = ()
            out['tree_method'] = 'trivial'
        else:
            for method, trial in _candidates(codes,rank):
                if out['tree_trials'] >= max_tree_trials:
                    out.update(reason='tree_trial_budget_exhausted')
                    return out
                out['tree_trials'] += 1
                if _valid(codes,trial):
                    edges = trial
                    out['tree_method'] = method
                    break
            if edges is None:
                out.update(reason='no_graphic_representation')
                return out
    # Recheck positive search results using exactly the public certificate.
    cert = {'basis_vectors':list(co.basis),'basis_edges':[list(e) for e in edges]}
    verify_graphic_certificate(groups,cert)
    out['certificate'] = cert
    cols = _columns(edges)
    target_image = _linear(target_code,cols)
    tables = []
    for g in groups:
        vals = [_linear(codes[x ^ g[0]],cols) for x in g]
        if len(vals)==1:
            shift = 0
        else:
            common = reduce(lambda a,b:a & b,vals[1:])
            if not common:
                raise AssertionError('edge images in a ternary group did not meet')
            shift = common & -common
        target_image ^= shift
        # Drop the ground coordinate 0. The linear image before translations
        # is even-weight, so this is injective on all possible differences.
        table = {(v ^ shift)>>1:x for x,v in zip(g,vals)}
        if len(table)!=len(g) or any(k.bit_count()>1 for k in table):
            raise AssertionError('recoded options are not distinct unit/zero masks')
        tables.append(table)
    matching = decide_unit_supports(tables,target_image>>1)
    out.update(status=matching['status'],matching=matching,matching_calls=1,
               reason='verified_graphic_matching')
    if matching['status']=='SAT':
        witness = [t[k] for t,k in zip(tables,matching['witness'])]
        if len(witness)!=len(groups) or any(x not in g for x,g in zip(witness,groups)) or reduce(xor,witness,0)!=rhs:
            raise AssertionError('graphic matching witness failed original choices')
        out['witness'] = witness
    return out
