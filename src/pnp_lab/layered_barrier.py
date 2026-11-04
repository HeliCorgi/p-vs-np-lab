"""Finite two-tag controls for the many-module ordinary-resolution barrier.

Small graphs test syntax/projections and small-cut assumptions only. They are
not an empirical proof of any asymptotic expansion or proof-length bound.
"""
from .simple_support import simple_support_image
from .width_transfer import cubic_tseitin


def graph_controls():
    q=10
    cycle={tuple(sorted((v,(v+1)%q))) for v in range(q)}
    matchings=(
        ((0,3),(1,5),(2,7),(4,8),(6,9)),
        ((0,3),(1,5),(2,8),(4,7),(6,9)),
        ((0,3),(1,6),(2,7),(4,9),(5,8)),
        ((0,3),(1,7),(2,6),(4,9),(5,8)))
    return tuple(tuple(sorted(cycle|set(m))) for m in matchings)


def make_layers(q,pairs):
    """Build k independent selector modules, selectors first (1..k)."""
    pairs=tuple(pairs);k=len(pairs);n=k;clauses=[];desc=[]
    for i,pair in enumerate(pairs):
        lo,hi=pair
        for b,edges in enumerate((lo,hi)):
            edge_count,raw=cubic_tseitin(q,edges)
            off=n;n+=edge_count
            ax=tuple(tuple((abs(l)+off)*(1 if l>0 else -1) for l in c) for c in raw)
            helpers=[]
            for c in ax:
                n+=1;helpers.append(n)
                # selected side b, when gate bit equals b
                guard=i+1 if b==0 else -(i+1)
                clauses.extend(((guard,c[0],n),(-n,c[1],c[2])))
            desc.append((i,b,ax,tuple(helpers)))
    return dict(n=n,k=k,cnf=tuple(clauses),modules=tuple(desc))


def completion_lift(instance,word):
    """Return a disjoint base conjunction, and literal images mapping into the full input."""
    k,n=instance['k'],instance['n']
    if type(word) is not int or not 0<=word<1<<k:raise ValueError('bad tag word')
    images=[j+1 for j in range(n)]
    for i in range(k):images[i]=bool(word>>i&1)
    base=[]
    for i,b,ax,helpers in instance['modules']:
        active=(word>>i&1)==b
        if active:base.extend(ax)
        for c,v in zip(ax,helpers):images[v-1]=-c[0] if active else False
    return tuple(base),tuple(images)


def blind_lift(instance,word):
    """Compose completion_lift with the simple-support gadget's signed copy map."""
    base,vmap=completion_lift(instance,word)
    m,cs,wires=simple_support_image(instance['n'],instance['cnf'])
    images=[True]*m
    for j,vs in enumerate(wires):
        for v in vs:images[v-1]=vmap[j]
    gates=tuple(vs[0] for vs in wires[:instance['k']])
    return base,cs,gates,tuple(images)
