"""Boolean width-three cyclic-four flows with independently renamed states on each edge."""
from itertools import combinations,product
from random import Random
from .ternary_flow import prism_edges,divergence,_solve_flow


def state_permutations(m,seed):
    rng=Random(seed);out=[]
    for _ in range(m):
        p=list(range(4));rng.shuffle(p);out.append(tuple(p))
    return tuple(out)


def four_flow(edges,charges,*,state_seed=14144):
    ed=tuple(tuple(e) for e in edges);qs=tuple(charges)
    if any(type(q) is not int or q not in range(4) for q in qs):raise ValueError('bad charges')
    if any(len(e)!=2 or e[0]==e[1] or any(type(v) is not int or not 0<=v<len(qs) for v in e) for e in ed):
        raise ValueError('bad edge')
    perm=state_permutations(len(ed),state_seed);rows=[];stars=[[] for _ in qs]
    for i,(a,b) in enumerate(ed):
        x=[5*i+1+j for j in range(5)]
        rows.extend((x[:2]+x[4:],[-x[4],x[2],x[3]]))
        rows.extend((-u,-v) for u,v in combinations(x[:4],2))
        stars[a].append((i,1));stars[b].append((i,-1))
    for v,star in enumerate(stars):
        if len(star)>3:raise ValueError('needs degree <=3')
        for word in product(range(4),repeat=len(star)):
            if sum(x*s for x,(_,s) in zip(word,star))%4!=qs[v]:
                rows.append(tuple(-(5*i+1+perm[i][x]) for x,(i,_) in zip(word,star)))
    return 5*len(ed),tuple(tuple(c) for c in rows)


def four_state_word(values,*,state_seed=14144):
    """One full Boolean model of all domain blocks for the named edge states."""
    ts=tuple(values)
    if any(type(t) is not int or not 0<=t<4 for t in ts):raise ValueError('bad state')
    word=0
    for i,(t,p) in enumerate(zip(ts,state_permutations(len(ts),state_seed))):
        j=p[t];word |= 1<<(5*i+j)
        if j>=2:word |= 1<<(5*i+4)
    return word


def four_prism_flow(k,bad=False,*,state_seed=14144):
    """Bad raises exactly one charge by two, preserving every parity equation."""
    es=prism_edges(k)
    vals=[(3*i+1)%4 for i in range(len(es))]
    qs=list(divergence(es,vals,2*k,4))
    if bad:qs[0]=(qs[0]+2)%4
    n,cs=four_flow(es,qs,state_seed=state_seed)
    return n,cs,(None if bad else four_state_word(vals,state_seed=state_seed))


def parity_lift(edges,charges,parities):
    """Give a Z4 flow for the specified mod-two flow, or None; independent of CNF."""
    es=tuple(edges);q=tuple(charges);t=tuple(parities)
    if any(x not in (0,1) for x in t) or len(t)!=len(es):raise ValueError('invalid parities')
    old=divergence(es,t,len(q),4)
    diff=[(a-b)%4 for a,b in zip(q,old)]
    if any(d%2 for d in diff):return None
    y=_solve_flow(es,[d//2 for d in diff],2)
    return None if y is None else tuple(u+2*v for u,v in zip(t,y))
