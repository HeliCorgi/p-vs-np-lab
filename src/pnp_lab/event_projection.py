"""Existential projection of the complement of a union of binary affine flats.

The current forbidden union is represented by canonical consistent equation
systems. Eliminating bit j keeps the assignments that admit EITHER bit value;
therefore the new forbidden union is the intersection of the two bad slices.
This decides existence, not multiplicity. No polynomial general bound claimed.
"""
from __future__ import annotations

from collections import defaultdict


def _reduced(rows):
    """Canonical high-pivot RREF; None is inconsistent, () means all points."""
    pivots = {}
    for x,b in rows:
        while x and x.bit_length()-1 in pivots:
            v,c = pivots[x.bit_length()-1]
            x ^= v
            b ^= c
        if not x:
            if b:
                return None
            continue
        pivots[x.bit_length()-1] = x,b
    for k in sorted(pivots):
        v,c = pivots[k]
        for p,(w,d) in pivots.items():
            if p>k and w & (1<<k):
                pivots[p]=(w^v,d^c)
    return tuple(pivots[k] for k in sorted(pivots,reverse=True))


def _input(n, events):
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative dimension.')
    raw=[]
    try:
        if isinstance(events,(str,bytes)): raise ValueError('Expected a list of events.')
        for e in events:
            if isinstance(e,(str,bytes)): raise ValueError('Invalid event.')
            rs=[]
            for a,b in e:
                if type(a) is not int or a<0 or a.bit_length()>n or type(b) is not int or b not in (0,1):
                    raise ValueError('Invalid mask or RHS for this dimension.')
                rs.append((a,int(b)))
            raw.append(tuple(rs))
    except TypeError as exc:
        raise ValueError('Expected events of affine equations.') from exc
    return raw


def _inside(x,event):
    return all((x&a).bit_count()%2 == b for a,b in event)


def _subset(A,B):
    """Does the solution flat A lie in B? Inputs consistent; B small rank first."""
    if len(A)<len(B): return False
    return _reduced(A+B)==A


def _hull_pair(A,B):
    # Equal normal systems, different RHS. In GF(2) their union is exactly
    # their joint hull: remove the single constraint distinguishing the cosets.
    i=next(i for i,((_,b),(_,c)) in enumerate(zip(A,B)) if b!=c)
    p,t=A[i]
    return _reduced((a^p,b^t) if b!=c else (a,b)
                    for j,((a,b),(_,c)) in enumerate(zip(A,B)) if j!=i)


def _simplify(items,counters):
    vals={e for e in items if e is not None}
    if () in vals: return ((),)
    while True:
        # Discard contained flats before looking for a parallel sister.
        live=[]
        for e in sorted(vals,key=lambda y:(len(y),y)):
            if any(len(g)<len(e) and _subset(e,g) for g in live):
                counters['contained_removed']+=1
            else: live.append(e)
        buckets=defaultdict(list)
        for e in live: buckets[tuple(a for a,_ in e)].append(e)
        nxt=set(); changed=False
        for eqs in buckets.values():
            for i in range(0,len(eqs)-1,2):
                v=_hull_pair(eqs[i],eqs[i+1])
                counters['parallel_merges']+=1
                if v==(): return ((),)
                nxt.add(v); changed=True
            if len(eqs)%2: nxt.add(eqs[-1])
        if not changed: return tuple(live)
        vals=nxt


def _slices(events,bit):
    common=[]; a=set(); b=set()
    for e in events:
        if all(not (mask&bit) for mask,_ in e):
            common.append(e); continue
        for sign,out in ((0,a),(1,b)):
            q=_reduced((mask&~bit, rhs ^ (sign if mask&bit else 0)) for mask,rhs in e)
            if q is not None: out.add(q)
    # Factors common to both bad slices can be retained without distributing.
    shared=a&b
    return common+sorted(shared), sorted(a-shared), sorted(b-shared)


def project_affine_events(n, events, *, order=None, max_pairs=None):
    """Exact unbudgeted decision and original bit witness. No count reported.

    Explicit order is a full permutation (first index eliminated first).
    Default greedily minimizes the product of slice sizes, with index tie-break.
    max_pairs charges tested cross-slice pairs only, not order selection,
    RREF or containment scans, trace storage, or count of input events.
    """
    raw=_input(n,events)
    if max_pairs is not None and (type(max_pairs) is not int or max_pairs<0):
        raise ValueError('max_pairs must be None or a nonnegative integer.')
    if order is not None:
        order=tuple(order)
        if len(order)!=n or any(type(i) is not int for i in order) or set(order)!=set(range(n)):
            raise ValueError('order must be a permutation of the bit indices.')
    out=dict(status='UNKNOWN',reason=None,witness=None,dimension=n,input_events=len(raw),
             projected_bits=[],pairs_tested=0,order_candidate_scans=0,
             peak_events=0,peak_live_intersections=0,parallel_merges=0,contained_removed=0,
             layer_sizes=[],max_pairs=max_pairs)
    flats=_simplify((_reduced(e) for e in raw),out)
    stages=[]; remaining=set(range(n))
    while True:
        out['peak_events']=max(out['peak_events'],len(flats))
        out['layer_sizes'].append(len(flats))
        if () in flats:
            out.update(status='UNSAT',reason='forbidden_union_is_full')
            return out
        if not flats: break
        if not remaining: raise AssertionError('A zero-dimensional nontrivial flat remains.')
        if order is None:
            key=None; chosen=None
            for j in sorted(remaining):
                c,a,b=_slices(flats,1<<j)
                out['order_candidate_scans']+=1
                cost=(len(a)*len(b),len(c),j)
                if key is None or cost<key: key,chosen=cost,(j,c,a,b)
            j,c,a,b=chosen
        else:
            j=order[len(stages)]; c,a,b=_slices(flats,1<<j)
        if max_pairs is not None and out['pairs_tested']+len(a)*len(b)>max_pairs:
            out.update(reason='pair_budget',next_bit=j,next_pair_count=len(a)*len(b))
            return out
        nxt=set(c)
        for left in a:
            for right in b:
                out['pairs_tested']+=1
                meet=_reduced(left+right)
                if meet is not None: nxt.add(meet)
        out['peak_live_intersections']=max(len(nxt),out['peak_live_intersections'])
        stages.append((j,flats));out['projected_bits'].append(j);remaining.remove(j)
        flats=_simplify(nxt,out)
    # Bits not explicitly eliminated are free once the remaining union is empty.
    x=0
    for j,layer in reversed(stages):
        if any(_inside(x,e) for e in layer):
            x |= 1<<j
            if any(_inside(x,e) for e in layer):
                raise AssertionError('Neither lifted bit makes the previous layer feasible.')
    if any(_inside(x,e) for e in raw):raise AssertionError('Bad lifted arrangement witness.')
    out.update(status='SAT',reason='checked_original_parameter_point',witness=x)
    return out
