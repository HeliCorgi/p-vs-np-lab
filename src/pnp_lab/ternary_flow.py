"""Width-three Boolean encodings of oriented flows over F2/F3, including shared bits.

Only fixtures/witness generation use edges, charges or port IDs. Refuters get
the raw CNF, including in the signed and reordered controls.
"""
from itertools import combinations, product
from random import Random


def prism_edges(k):
    """Two disjoint oriented k-cycles, with k rungs; cubic for every k>=3."""
    if type(k) is not int or k<3:raise ValueError('prism length must be >=3')
    return tuple((r*k+i,r*k+(i+1)%k) for r in range(2) for i in range(k))+tuple((i,k+i) for i in range(k))


def _encode(edges,charges,p,offset=0,ports=None):
    if p not in (2,3) or type(p) is not int:raise ValueError('expected modulus 2 or 3')
    ed=tuple(tuple(e) for e in edges);charges=tuple(charges)
    if not charges or any(type(q) is not int or not 0<=q<p for q in charges):raise ValueError('invalid charges')
    if any(len(e)!=2 or any(type(v) is not int or not 0<=v<len(charges) for v in e) or e[0]==e[1] for e in ed):
        raise ValueError('invalid oriented edge')
    ports=dict(ports or {});stars=[[] for _ in charges];clauses=[]
    if any(type(v) is not int or not 0<=v<len(stars) or type(x) is not int or not 1<=x<=offset for v,x in ports.items()):
        raise ValueError('ports must be separate earlier coordinates')
    w=3 if p==3 else 1
    for i,(a,b) in enumerate(ed):
        stars[a].append((i,1));stars[b].append((i,-1))
        if p==3:
            block=tuple(offset+3*i+1+j for j in range(3))
            clauses.append(block)
            clauses.extend((-u,-v) for u,v in combinations(block,2))
    for v,star in enumerate(stars):
        if len(star)+int(v in ports)>3:raise ValueError('vertex not encodable at width three')
        for tup in product(range(p),repeat=len(star)):
            div=sum(s*t for (_,s),t in zip(star,tup))
            row=tuple(-(offset+3*i+1+t) if p==3 else (offset+i+1)*(-1 if t else 1)
                      for (i,_),t in zip(star,tup))
            if v not in ports:
                if (div-charges[v])%p:clauses.append(row)
            else:
                for b in (0,1):
                    if (div-charges[v]-b)%p:clauses.append(row+(ports[v]*(-1 if b else 1),))
    return offset+w*len(ed),tuple(clauses)


def onehot_flow(edges,charges,modulus=3):
    """With modulus 3 use three indicators per edge; with 2 use one bit."""
    return _encode(edges,charges,modulus)


def divergence(edges,values,nv,p):
    out=[0]*nv
    if len(edges)!=len(values):raise ValueError('length mismatch')
    for (u,v),x in zip(edges,values):
        out[u]=(out[u]+x)%p;out[v]=(out[v]-x)%p
    return tuple(out)


def _word(values,p,offset=0):
    return sum(1<<(offset+3*i+t if p==3 else offset+i) for i,t in enumerate(values) if p==3 or t)


def prism_flow(k,bad=False,*,modulus=3):
    """Return n, CNF, and a checked SAT word or None. Twins differ at vertex 0."""
    ed=prism_edges(k);p=modulus
    if p not in (2,3):raise ValueError('unsupported modulus')
    ts=[(i+1)%p for i in range(len(ed))]
    q=list(divergence(ed,ts,2*k,p))
    if not any(q):
        ts[0]=(ts[0]+1)%p;q=list(divergence(ed,ts,2*k,p))
    if bad:q[0]=(q[0]+1)%p
    n,f=onehot_flow(ed,q,p)
    return n,f,(None if bad else _word(ts,p))


def scramble(n,cs,word,seed):
    """Common signed renaming and row/literal reorder; no generator data in CNF."""
    rng=Random(seed);perm=list(range(1,n+1));rng.shuffle(perm)
    perm=[v if rng.randrange(2) else -v for v in perm]
    out=[]
    for c in cs:
        r=[perm[abs(l)-1]*(1 if l>0 else -1) for l in c];rng.shuffle(r);out.append(tuple(r))
    rng.shuffle(out)
    y=None if word is None else sum(1<<(abs(v)-1) for j,v in enumerate(perm) if bool(word>>j&1)==(v>0))
    return tuple(out),y


def _port_graph(k):
    ed=prism_edges(k)
    # Subdivide three different rungs, making one degree-two port per rung.
    rows=[];nv=2*k
    for j,(a,b) in enumerate(ed):
        if 2*k<=j<2*k+3:
            w=nv+j-2*k
            rows.extend([(a,w),(w,b)])
        else:rows.append((a,b))
    return tuple(rows),tuple(range(nv,nv+3))


def mixed_port_flow(k,*,binary_rhs=1,ternary_rhs=2):
    """Return n, cnf, three shared Boolean ports, and construction-only metadata.

    The projections are sum(ports)=rhs in each field. Neither bank is
    permitted access to the internal edges of the other bank.
    """
    if type(binary_rhs) is not int or not 0<=binary_rhs<2 or type(ternary_rhs) is not int or not 0<=ternary_rhs<3:
        raise ValueError('rhs outside field')
    ed,pv=_port_graph(k);ports=(1,2,3);pd=dict(zip(pv,ports))
    qs=[0]*(2*k+3);qs[0]=(-binary_rhs)%2
    n2,f=_encode(ed,qs,2,3,pd)
    qs[0]=(-ternary_rhs)%3
    n3,g=_encode(ed,qs,3,n2,pd)
    return n3,f+g,ports,dict(binary=f,ternary=g,edges=ed,port_vertices=pv,ternary_offset=n2)


def _solve_flow(ed,demand,p):
    """Solve incidence equations along a spanning tree; independent of CNF."""
    inc=[[] for _ in demand]
    for i,(u,v) in enumerate(ed):
        inc[u].append((v,i,1));inc[v].append((u,i,-1))
    parent={0:None};queue=[0]
    for u in queue:
        for v,i,s in inc[u]:
            if v not in parent:parent[v]=(u,i,-s);queue.append(v)
    if len(queue)!=len(demand):raise ValueError('disconnected fixture')
    delta=list(demand);word=[0]*len(ed)
    for v in reversed(queue[1:]):
        u,i,sign=parent[v]
        word[i]=sign*delta[v]%p
        delta[u]=(delta[u]+delta[v])%p
    return None if delta[0]%p else tuple(word)


def mixed_half_witness(k,bits,*,prime,rhs):
    bits=tuple(bits)
    if len(bits)!=3 or any(type(b) is not int or b not in (0,1) for b in bits) or prime not in (2,3):
        raise ValueError('bad port values/field')
    ed,pv=_port_graph(k);demand=[0]*(2*k+3);demand[0]=(-rhs)%prime
    for v,b in zip(pv,bits):demand[v]=b
    word=_solve_flow(ed,demand,prime)
    if word is None:return None
    port=sum(b<<i for i,b in enumerate(bits))
    return port|_word(word,prime,3+(len(ed) if prime==3 else 0))


def mixed_port_witness(k,bits,*,binary_rhs=1,ternary_rhs=2):
    bits=tuple(bits)
    a=mixed_half_witness(k,bits,prime=2,rhs=binary_rhs)
    b=mixed_half_witness(k,bits,prime=3,rhs=ternary_rhs)
    return None if a is None or b is None else (a|b)
