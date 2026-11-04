"""Finite ten-vertex controls for the clause-by-clause transport barrier.

No expansion or unbounded lower bound is inferred from the two graphs.
Variables are the sorted undirected graph edges; edge variable 1 corresponds
to edges[0]. The only charge in an odd instance is at vertex 0.
"""
from itertools import combinations,product


NAMES=('petersen','pentagonal-prism')


def cubic_control(name,odd=True):
    if name not in NAMES or type(odd) is not bool:raise ValueError('invalid graph or charge')
    jump=2 if name=='petersen' else 1
    edges=tuple(sorted({tuple(sorted(e)) for i in range(5) for e in (
        (i,(i+1)%5),(i+5,5+(i+jump)%5),(i,i+5))}))
    stars=[tuple(j for j,e in enumerate(edges,1) if v in e) for v in range(10)]
    cs=[]
    for v,vs in enumerate(stars):
        for bits in product((0,1),repeat=3):
            if sum(bits)%2!=int(odd and v==0):
                cs.append(tuple(-e if b else e for b,e in zip(bits,vs)))
    return edges,tuple(cs)


def components(edges,deleted):
    """Vertex components after deleting the specified one-based edge IDs."""
    nbr=[[] for _ in range(10)];deleted=set(deleted)
    for j,(u,v) in enumerate(edges,1):
        if j not in deleted:nbr[u].append(v);nbr[v].append(u)
    seen=set();out=[]
    for r in range(10):
        if r in seen:continue
        comp=[r];seen.add(r)
        for v in comp:
            for w in nbr[v]:
                if w not in seen:seen.add(w);comp.append(w)
        out.append(tuple(sorted(comp)))
    return sorted(out,key=lambda c:(len(c),c))


def four_cycles(edges):
    """Count unoriented cycles by opposite vertices and common neighbors."""
    adj=[set() for _ in range(10)]
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    c=0
    for u,v in combinations(range(10),2):
        t=len(adj[u]&adj[v]);c+=t*(t-1)//2
    return c//2


def critical_assignment(edges,clause):
    """Construct a word falsifying just this raw clause of the odd instance."""
    star=tuple(sorted(abs(l) for l in clause))
    vs=set(range(10))
    for i in star:vs &= set(edges[i-1])
    if len(vs)!=1 or len(star)!=3:raise ValueError('not a cubic star')
    cut=vs.pop()
    nbr=[[] for _ in range(10)]
    word=sum(1<<(abs(l)-1) for l in clause if l<0)
    demand=[int(v==0) for v in range(10)]
    for i,(a,b) in enumerate(edges,1):
        if cut in (a,b):
            if word>>(i-1)&1:demand[a]^=1;demand[b]^=1
        else:nbr[a].append((b,i));nbr[b].append((a,i))
    if not demand[cut]:raise ValueError('local pattern does not violate its star')
    start=next(u for u in range(10) if u!=cut)
    order=[start];parent={start:None}
    for u in order:
        for v,e in nbr[u]:
            if v not in parent:parent[v]=(u,e);order.append(v)
    if len(order)!=9:raise ValueError('remainder must be connected')
    for v in reversed(order[1:]):
        u,e=parent[v]
        if demand[v]:word|=1<<(e-1);demand[u]^=1
    if demand[start]:raise ValueError('incompatible remainder')
    return word


def gated_cubic_siblings(odd=True):
    """Return ambient dimension, source 3-CNF, selector, naked sides, lift maps.

    At selector=side (0 or 1) the corresponding naked CNF is active. Each
    lift map sends a word on the naked edge coordinates 1..15 into the
    corresponding sibling. Both naked sources may be considered over the
    full ambient scope, with every other coordinate unused.
    """
    cs=[cubic_control(name,odd)[1] for name in NAMES]
    s=16;n=s;f=[];maps=[list(range(1,n+1)) for _ in range(2)]
    for side,formula in enumerate(cs):
        for a,b,c in formula:
            n+=1;g=s if side==0 else -s
            f.extend(((g,a,n),(-n,b,c)))
            for t,mp in enumerate(maps):mp.append(-a if side==t else False)
    return n,tuple(f),s,tuple(cs),tuple(tuple(mp) for mp in maps)


def sibling_at(clauses,selector,side):
    return tuple(tuple(l for l in c if abs(l)!=selector) for c in clauses
                 if not any(abs(l)==selector and bool(side)==(l>0) for l in c))


def finite_ceiling(name):
    """Enumerate all small supports/patterns, with no proof-complexity extrapolation."""
    edges,cs=cubic_control(name);axioms={frozenset(c) for c in cs}
    connected=singleton=raw=other=spared=bad=0
    for d in range(4):
        for support in combinations(range(1,16),d):
            parts=components(edges,support)
            if len(parts)==1:connected+=1
            elif len(parts)==2 and [len(c) for c in parts]==[1,9] and d==3:
                singleton+=1
            else:raise AssertionError('unexpected cut topology')
            for bits in product((0,1),repeat=d):
                c=frozenset(-e if b else e for e,b in zip(support,bits))
                israw=(c in axioms)
                if israw:raw+=1
                else:other+=1
                if len(parts)==2:
                    v=parts[0][0]
                    if sum(bits)%2!=int(v==0):
                        bad+=1
                        if not israw:raise AssertionError('non-raw clause killed an isolated star')
                    else:
                        spared+=1
                        if israw:raise AssertionError('raw clause left star valid')
                elif israw:raise AssertionError('raw star should be disconnected')
    return dict(graph=name,connected_supports=connected,isolated_vertex_supports=singleton,
                width_at_most_three_raw=raw,width_at_most_three_nonraw=other,
                falsifications_with_violated_isolated_star=bad,
                falsifications_with_satisfied_isolated_star=spared,unoriented_four_cycles=four_cycles(edges))
