"""Merge full affine flats and affine flats missing one point without listing their points.

Explicit supports have at most three distinct choices. A stalled pair reduction
is inconclusive; outside-hull contradictions and direct-sum negative answers
are exact. SAT always includes independently checked original choices.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import reduce
from operator import xor

from .frontier import _read_groups, affine_core


class _Rows:
    """Echelon vectors with linear tags, returning the tag accumulated by a reduction."""
    def __init__(self):
        self.rows = {}

    def solve(self, value):
        tag = 0
        while value:
            pair = self.rows.get(value.bit_length()-1)
            if pair is None:
                break
            value ^= pair[0]
            tag ^= pair[1]
        return value, tag

    def add(self, value, tag):
        rest, old = self.solve(value)
        if rest:
            self.rows[rest.bit_length()-1] = (rest, old ^ tag)
        return rest, old ^ tag


@dataclass
class _Flat:
    anchor: int
    dirs: tuple[int, ...]
    hole: int | None
    index: int | None = None
    children: tuple[_Flat, _Flat] | None = None
    splitter: _Rows | None = None
    common: tuple[int, ...] = ()


def _join(a, b):
    # Tag a direction of P with itself and a direction of Q with zero.
    # A dependency during Q insertion identifies a vector shared by P and Q.
    rows = _Rows()
    for v in a.dirs:
        rows.add(v, v)
    common = []
    for v in b.dirs:
        rest, shared = rows.add(v, 0)
        if not rest:
            common.append(shared)
    k = len(common)
    if a.hole is None and b.hole is None:
        hole = None
    elif k >= 2 or (k == 1 and (a.hole is None or b.hole is None)):
        hole = None
    elif k == 1:
        hole = a.hole ^ b.hole ^ common[0]
    elif not a.dirs and a.hole is None:
        hole = a.anchor ^ b.hole
    elif not b.dirs and b.hole is None:
        hole = b.anchor ^ a.hole
    else:
        return None
    return _Flat(a.anchor ^ b.anchor, tuple(row for row,_ in rows.rows.values()),
                 hole, children=(a,b), splitter=rows, common=tuple(common[:2]))


def _split_at(node, target):
    a,b = node.children
    delta = target ^ a.anchor ^ b.anchor
    rest, left_dir = node.splitter.solve(delta)
    if rest:
        raise AssertionError('Asked to split outside the joined affine hull.')
    left = a.anchor ^ left_dir
    # At most two decompositions are forbidden. Up to three distinct points
    # in the fiber suffice, even when the full fiber has exponentially many.
    for offset in (0, *node.common):
        x = left ^ offset
        y = target ^ x
        if x != a.hole and y != b.hole:
            return x,y
    raise AssertionError('No surviving decomposition of a represented point.')


def decide_hole_flats(supports, rhs, *, cover=False):
    """Decide by symbolic pair sums, returning UNKNOWN when unresolved dependencies remain.

    This deterministic polynomial-time *partial* procedure tries one particular
    solution of the last affine relaxation. When that hits a hole and the
    decomposition is nonunique it never reports UNSAT on that basis. Set
    cover=True to try a constructive exclusion-count bound on such fibers.
    """
    if type(cover) is not bool:
        raise ValueError("cover must be a Boolean.")
    groups = _read_groups(supports)
    if any(len(g)>3 for g in groups):
        raise ValueError('hole-flat backend requires at most three distinct options per group.')
    core = affine_core(groups,rhs)
    out = dict(status='UNKNOWN', reason=None, witness=None, affine_groups=len(core.absorbed),
               affine_rank=len(core.basis), input_groups=len(groups), residual_groups=len(core.residual),
               pair_tests=0, merges=0, full_merges=0, one_hole_merges=0,
               final_flats=0, max_flat_rank=0, final_hull_rank=0,
               decomposition_nullity=0, split_nodes=0)
    if any(not g for g in groups):
        out.update(status='UNSAT',reason='empty_support')
        return out

    nodes=[]
    for i,g in enumerate(core.supports):
        # Fixed-point affine preprocessing leaves exactly ternary supports.
        if len(g)!=3:
            raise AssertionError('Unexpected residual support after affine absorption.')
        a,b,c=g
        nodes.append(_Flat(a,(a^b,a^c),a^b^c,index=i))
    if nodes:
        out['max_flat_rank']=2
    # Fixed first-fit order for reproducibility. Pairs failing a test can
    # become mergeable later, so rescan after every successful merge.
    while True:
        joined=False
        for i in range(len(nodes)):
            for j in range(i+1,len(nodes)):
                out['pair_tests'] += 1
                merged=_join(nodes[i],nodes[j])
                if merged is None:
                    continue
                nodes[i]=merged
                del nodes[j]
                out['merges']+=1
                out['full_merges' if merged.hole is None else 'one_hole_merges']+=1
                out['max_flat_rank']=max(out['max_flat_rank'],len(merged.dirs))
                joined=True
                break
            if joined:
                break
        if not joined:
            break

    # Determine one direction choice from each flat with the requested sum.
    rows=_Rows()
    dimension=0
    for node in nodes:
        for d in node.dirs:
            rows.add(d,1<<dimension)
            dimension+=1
    rest,code=rows.solve(reduce(xor,(n.anchor for n in nodes),core.target))
    nullity=dimension-len(rows.rows)
    out.update(final_flats=len(nodes),final_hull_rank=len(rows.rows),decomposition_nullity=nullity)
    if rest:
        out.update(status='UNSAT',reason='outside_joint_affine_hull')
        return out
    stack=[]
    at=0
    for node in nodes:
        v=node.anchor
        for d in node.dirs:
            if code & (1<<at):
                v^=d
            at+=1
        stack.append((node,v))
    if any(value==node.hole for node,value in stack):
        if not nullity:
            out.update(status='UNSAT', reason='forced_hole')
            return out
        if not cover:
            out.update(reason='dependent_flats_hit_hole')
            return out
        from .flat_cover import solve_hole_cover
        extra=solve_hole_cover([(n.anchor,n.dirs,n.hole) for n in nodes], core.target)
        out['cover_evidence']={k:v for k,v in extra.items() if k!='witness'}
        if extra['status']!='SAT':
            out.update(status=extra['status'],reason='cover_'+extra['reason'])
            return out
        if (len(extra['witness'])!=len(nodes) or reduce(xor,extra['witness'],0)!=core.target
                or any(v==n.hole for n,v in zip(nodes,extra['witness']))):
            raise AssertionError('Invalid avoidance witness.')
        stack=list(zip(nodes,extra['witness']))

    chosen=[None]*len(core.residual)
    while stack:
        node,value=stack.pop()
        if node.children is None:
            chosen[node.index]=value
        else:
            x,y=_split_at(node,value)
            stack.extend(zip(node.children,(x,y)))
            out['split_nodes']+=1
    witness=core.lift(chosen)
    if len(witness)!=len(groups) or any(x not in g for x,g in zip(witness,groups)) or reduce(xor,witness,0)!=rhs:
        raise AssertionError('Symbolic witness failed original constraints.')
    out.update(status='SAT',reason='checked_original_witness',witness=witness)
    return out
