"""Put every matching of q labelled cubic vertex stars in one raw 3-CNF.

These constructors describe limbs of a full restriction tree, NOT an
algorithm required to visit those limbs. The all-switches-false subtree
even admits an immediate satisfying assignment.
"""
from itertools import combinations, product


def _size(q):
    if type(q) is not int or q<4 or q%2:
        raise ValueError('expected an even number >=4 of cubic vertices')
    p=3*q
    return p,p*(p-1)//2


def port_formula(q):
    """Return (declared variable count, tag count, clauses). True tags enable a wire."""
    p,t=_size(q)
    cs=[]
    for v in range(q):
        vs=tuple(t+3*v+i+1 for i in range(3))
        for bits in product((0,1),repeat=3):
            if sum(bits)%2!=int(v==0):
                cs.append(tuple(-l if b else l for l,b in zip(vs,bits)))
    for j,(a,b) in enumerate(combinations(range(t+1,t+p+1),2),1):
        cs.extend(((-j,-a,b),(-j,a,-b)))
    return t+p,t,tuple(cs)


def matching_instance(q,edges):
    """Choose a tag word for a simple labelled cubic graph.

    Under pull, both endpoint ports of a matched edge map to its one naked
    edge bit. Representatives choose one port per edge for the reverse
    derivations; no assertion about other completed tag words is made.
    """
    p,t=_size(q)
    edges=tuple(sorted(tuple(e) for e in edges))
    if any(len(e)!=2 or any(type(v) is not int for v in e) or not 0<=e[0]<e[1]<q for e in edges):
        raise ValueError('expected sorted simple edge endpoints')
    if len(set(edges))!=len(edges):raise ValueError('parallel edges')
    incidence=[[] for _ in range(q)]
    for j,(v,w) in enumerate(edges,1):
        incidence[v].append(j);incidence[w].append(j)
    if any(len(ids)!=3 for ids in incidence):raise ValueError('expected cubic graph')
    # Node labels need not be recovered. Only valid matching assignments
    # use this deterministic incidence order in the test encodings.
    port_edge=tuple(e for ids in incidence for e in ids)
    ends=[[] for _ in edges]
    for i,e in enumerate(port_edge,t+1):ends[e-1].append(i)
    pairs={tuple(x) for x in ends}
    n,_,cs=port_formula(q)
    tagmask=sum(1<<(j-1) for j,ab in enumerate(combinations(range(t+1,n+1),2),1) if ab in pairs)
    residual=tuple(tuple(l for l in c if abs(l)>t) for c in cs
                   if not any(abs(l)<=t and bool(tagmask & (1<<(abs(l)-1)))==(l>0) for l in c))
    return dict(n=n,t=t,tagmask=tagmask,residual=residual,edges=edges,endpoints=tuple(map(tuple,ends)),
                pull=(False,)*t+port_edge,reps=tuple(x[0] for x in ends))


def representative_proof(instance):
    """Ordinary resolution traces for all naked star axioms on representative ports.

    Returned line indices follow width_transfer.replay. Resolving with
    the appropriate wire axiom changes one port of a clause at a time.
    """
    R=instance['residual'];t=instance['t']; images=instance['pull'];reps=instance['reps']
    rows=[frozenset(c) for c in R];ax={c:i for i,c in enumerate(rows)}
    proof=[('a',i) for i in range(len(rows))]
    lines=[]
    for i,c in enumerate(R):
        if len(c)!=3:continue
        at=i;current=rows[i]
        for l in c:
            port=abs(l)
            if port<=t:raise ValueError('not tag restricted')
            p=reps[images[port-1]-1]*(1 if l>0 else -1)
            if l==p:continue
            eq=ax[frozenset((-l,p))]
            a,b=(at,eq) if l>0 else (eq,at)
            proof.append(('r',a,b,port))
            current=(current-{l})|{p}
            rows.append(current);at=len(rows)-1
        lines.append(at)
    return proof,lines
