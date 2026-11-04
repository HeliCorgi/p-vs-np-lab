"""Tagged Tseitin 3-CNFs with pairwise transport-incomparable restrictions.

After instantiating every tag the unsigned supports alone recover all tag
values, even after renaming and complementing active variables.
"""
from collections import Counter, defaultdict
from itertools import product


def _parity(vs, rhs):
    return tuple(tuple(-v if b else v for v,b in zip(vs,bits))
                 for bits in product((0,1), repeat=len(vs)) if sum(bits)%2 != rhs)


def switch_tseitin(k, *, odd=True):
    if type(k) is not int or k<1 or type(odd) is not bool:
        raise ValueError("k must be positive; odd must be boolean")
    n=k
    clauses=[]
    def vertex(deg,b=0):
        nonlocal n
        vs=tuple(range(n+1,n+deg+1));n+=deg
        clauses.extend(_parity(vs,b));return vs
    def eq(a,b,guard=None):
        for cl in ((-a,b),(a,-b)):
            clauses.append(cl if guard is None else (guard,*cl))
    def chain(left,interior,right):
        return {(min(x,y),max(x,y)) for x,y in
                zip([left]+[p[1] for p in interior],[p[0] for p in interior]+[right])}
    r=2*k+2
    cube=[vertex(3,int(odd and i==0)) for i in range(r)]
    for i in range(r//2):eq(cube[i][2],cube[i+r//2][2])
    for j in range(k):
        u=[vertex(2) for _ in range(5)]
        a,b=cube[2*j][1],cube[2*j+1][0]
        c,d=cube[2*j+1][1],cube[2*j+2][0]
        def wires(split):return chain(a,u[:split],b)|chain(c,u[split:],d)
        p,q=wires(1),wires(2)
        for x,y in sorted(p&q):eq(x,y)
        for x,y in sorted(p-q):eq(x,y,j+1)
        for x,y in sorted(q-p):eq(x,y,-(j+1))
    for i,length in ((r-2,6),(r-1,7)):
        interior=[vertex(2) for _ in range(length-1)]
        for x,y in sorted(chain(cube[i][1],interior,cube[(i+1)%r][0])):eq(x,y)
    return n,tuple(clauses)


def restrict(cs,d,word):
    if type(d) is not int or d<0 or type(word) is not int or not 0<=word<1<<d:
        raise ValueError("invalid prefix")
    return tuple(tuple(l for l in c if abs(l)>d) for c in cs
                 if not any(abs(l)<=d and bool(word & (1<<(abs(l)-1))) == (l>0) for l in c))


def _scopes(cs):
    groups=defaultdict(set)
    for c in cs:
        if not c or len(c)>3 or any(type(l) is not int or l==0 for l in c) or len({abs(l) for l in c})!=len(c):
            raise ValueError("expected nonempty proper 3-clauses")
        c=tuple(sorted(c,key=abs))
        groups[tuple(map(abs,c))].add(c)
    return groups


def _complete(vs,clauses):
    for rhs in (0,1):
        if clauses==set(_parity(vs,rhs)):return rhs
    return None


def decode_word(cs):
    """Read path lengths of one completed CNF, ignoring all variable names/signs.

    Does not recognize arbitrary inputs as UNSAT; meant as an isomorphism
    invariant on the constructed family. Cubic stars are graph vertices;
    variables link the two star scopes in which they occur.
    """
    vertices=list(_scopes(cs))
    byvar=defaultdict(list)
    for i,vs in enumerate(vertices):
        for v in vs:byvar[v].append(i)
    nbr=[[] for _ in vertices]
    for pair in byvar.values():
        if len(pair)!=2:raise ValueError("not a full incidence instance")
        a,b=pair;nbr[a].append(b);nbr[b].append(a)
    cycle=defaultdict(list)
    for start in range(len(nbr)):
        if len(nbr[start])!=3:continue
        for cur in nbr[start]:
            prev=start;length=1
            while len(nbr[cur])==2:
                p,q=nbr[cur];prev,cur=cur,(p if q==prev else q);length+=1
            if length>2:cycle[start].append((cur,length))
    if not cycle or any(len(ns)!=2 for ns in cycle.values()):raise ValueError("no decoded cycle")
    hubs=[v for v,ns in cycle.items() if {dist for _,dist in ns}=={12,14}]
    if len(hubs)!=1:raise ValueError("missing sentinels")
    prev=hubs[0];cur=next(v for v,l in cycle[prev] if l==14)
    ds=[]
    while cur!=hubs[0]:
        opts=[(v,l) for v,l in cycle[cur] if v!=prev]
        if len(opts)!=1 or len(ds)>len(cycle):raise ValueError("invalid cycle")
        nxt,dist=opts[0];ds.append(dist);prev,cur=cur,nxt
    if ds.pop()!=12 or len(ds)%2:raise ValueError("invalid code")
    result=0
    for i in range(0,len(ds),2):
        pair=ds[i:i+2]
        if pair==[6,8]:result |= 1 << (i//2)
        elif pair!=[4,10]:raise ValueError("invalid bit lengths")
    return result


def _model(n,eqs):
    piv={}
    for v,b in eqs:
        while v:
            j=v.bit_length()-1
            if j not in piv:piv[j]=(v,b);break
            u,c=piv[j];v^=u;b^=c
        else:
            if b:return None
    x=0
    for j,(v,b) in sorted(piv.items()):
        if (v&x).bit_count()%2!=b:x|=1<<j
    return x


def critical_model(n,cs,k,deleted):
    """Model falsifying only deleted clause of a (possibly partial) odd instance."""
    target=cs[deleted]
    # Choose the unique guard value activating this clause, if any.
    tags=sum(1<<(abs(l)-1) for l in target if abs(l)<=k and l<0)
    full=restrict(cs,k,tags)
    surviving=tuple(sorted((l for l in target if abs(l)>k),key=abs))
    skip=tuple(map(abs,surviving));eq=[]
    groups=_scopes(full)
    if surviving not in groups[skip]:raise ValueError("removed clause is not active")
    for vs,cs0 in groups.items():
        b=_complete(vs,cs0)
        if b is None:raise ValueError("incomplete parity orbit")
        if vs!=skip:eq.append((sum(1<<(v-1) for v in vs),b))
    eq.extend((1<<(abs(l)-1),int(l<0)) for l in surviving)
    x=_model(n,eq)
    if x is None:raise AssertionError("no critical assignment")
    return x|tags


def conservation_refutation(n,cs):
    """Try a cheap named-clause proof; return a certificate or None, never infer SAT.

    Unconditional complete parity orbits give equations. For each prospective
    guard bit, XOR all equality edges certified on its 0-slice and its 1-slice.
    An identical sum is an unconditional consequence. This suffices for our
    entire obstruction at the root (does not use the designated tag IDs).
    """
    if type(n) is not int or n<0:raise ValueError("invalid variable count")
    groups=_scopes(cs);rows=[]; guards=defaultdict(lambda:[set(),set()])
    for vs,clauses in groups.items():
        if max(vs)>n:raise ValueError("out of scope")
        mask=sum(1<<(a-1) for a in vs)
        b=_complete(vs,clauses)
        if b is not None:rows.append((mask,b,('star',vs,b)))
        if len(vs)!=3:continue
        for g in vs:
            pair=tuple(v for v in vs if v!=g)
            for b in (0,1):
                sign=-g if b else g
                needed={tuple(sorted((sign,*c),key=abs)) for c in _parity(pair,0)}
                if needed<=clauses:guards[g][b].add(pair)
    for tag,(aa,bb) in sorted(guards.items()):
        def total(edges):
            x=0
            for u,v in edges:x^=(1<<(u-1))|(1<<(v-1))
            return x
        m=total(aa)
        if m and m==total(bb):
            rows.append((m,0,('guard',tag,tuple(sorted(aa)),tuple(sorted(bb)))))
    mask=rhs=0
    for m,b,_ in rows:mask^=m;rhs^=b
    if not mask and rhs:return [reason for _,_,reason in rows]
    return None


def verify_conservation(n,cs,proof):
    """Replay only listed star / branch derivations directly against raw clauses."""
    if type(n) is not int or n<0:return False
    try:
        clauses={frozenset(c) for c in cs}
        total=rhs=0
        for row in proof:
            kind=row[0]
            if kind=='star':
                _,vs,b=row
                if (not 1<=len(vs)<=3 or type(b) is not int or b not in (0,1)
                    or len(set(vs))!=len(vs) or any(type(v) is not int or not 1<=v<=n for v in vs)):
                    return False
                if not all(frozenset(cl) in clauses for cl in _parity(vs,b)):return False
                for v in vs:total^=1<<(v-1)
                rhs^=b
            elif kind=='guard':
                _,g,left,right=row
                if type(g) is not int or not 1<=g<=n:return False
                sums=[]
                for sign,edges in ((g,left),(-g,right)):
                    mask=0
                    for u,v in edges:
                        if type(u) is not int or type(v) is not int or not 1<=min(u,v)<=max(u,v)<=n or len({g,u,v})!=3:return False
                        if not all(frozenset(cl) in clauses for cl in ((sign,-u,v),(sign,u,-v))):return False
                        mask ^= (1<<(u-1))|(1<<(v-1))
                    sums.append(mask)
                if sums[0]!=sums[1]:return False
                total ^= sums[0]
            else:return False
        return total==0 and rhs==1
    except (IndexError,ValueError,TypeError):return False
