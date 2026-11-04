"""Polynomially checkable, directional maps from 3-CNF A models to B models.

Image entry j is a signed 1-based source literal or a Boolean constant, and
specifies target variable j+1. A certified map does not require finding any
A-model. None from the finder means no certificate found, not nonexistence.
"""
from __future__ import annotations

from collections import defaultdict
from functools import lru_cache
from itertools import combinations

from .decision_labels import canonical_cnf
from .observation_2sat import _base as _solve_binary_forbidden_patterns


KIND = "signed-substitution-v1"


def _raw(n, cnf):
    if type(n) is not int or n < 0 or isinstance(cnf,(str,bytes)):
        raise ValueError("Expected nonnegative explicit scope and a 3-CNF.")
    rows = []
    try:
        for c in cnf:
            if isinstance(c,(str,bytes)): raise ValueError("Invalid clause.")
            row = tuple(c)
            if len(row)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in row):
                raise ValueError("Invalid signed width-three clause.")
            rows.append(row)
    except TypeError as e:
        raise ValueError("Expected clauses of literals.") from e
    return tuple(rows)


def _images(n, cert):
    if type(n) is not int or n<0 or not isinstance(cert,dict) or cert.get("kind")!=KIND:
        return None
    v=cert.get("images")
    if not isinstance(v,(tuple,list)) or len(v)!=n or any(type(x) is not bool and
            (type(x) is not int or not 1<=abs(x)<=n) for x in v):
        return None
    return v


def check_transport(n, source, target, cert):
    """Check each raw target clause without using any discovery algorithm.

    Malformed certificates are rejected; invalid input CNFs raise ValueError.
    Extra metadata (including the discovery method) is not trusted.
    """
    a,b=_raw(n,source),_raw(n,target)
    images=_images(n,cert)
    if images is None:return False
    source_clauses={frozenset(c) for c in a}
    for clause in b:
        pulled=set()
        for l in clause:
            v=images[abs(l)-1]
            if type(v) is bool:
                if v==(l>0): break
            else:
                p=v if l>0 else -v
                if -p in pulled:break
                pulled.add(p)
        else:
            # Enumerate at most eight subsets of a pulled-back clause.
            if not any(frozenset(s) in source_clauses for j in range(len(pulled)+1)
                       for s in combinations(pulled,j)):return False
    return True


def apply_transport(n, cert, source_mask):
    """Evaluate the image word. Source satisfiability is the caller's premise."""
    images=_images(n,cert)
    if images is None or type(source_mask) is not int or source_mask<0 or source_mask.bit_length()>n:
        raise ValueError("Malformed substitution or source word.")
    return sum(1<<j for j,v in enumerate(images)
               if (v if type(v) is bool else ((source_mask>>(abs(v)-1)&1)==(v>0))))


def _pack(v,method):
    return dict(kind=KIND,images=list(v),method=method)


def _group(f):
    out=defaultdict(set)
    for c in f:
        ids=tuple(abs(v)-1 for v in c)
        out[ids].add(sum(1<<i for i,v in enumerate(c) if v<0))
    return out


def _local(a,b):
    # For each target sign word t, t XOR shift must be a sign word whose
    # clause contains some source clause. Constraints span <=3 columns.
    ag,bg=_group(a),_group(b)
    aset=set(map(frozenset,a))
    local=[]; exact=[]
    balanced=ag.keys()==bg.keys() and all(len(ag[p])==len(bg[p]) for p in bg)
    for p,T in bg.items():
        words=range(1<<len(p))
        good=set()
        for w in words:
            q=tuple(-(j+1) if w>>i&1 else j+1 for i,j in enumerate(p))
            if any(frozenset(s) in aset for k in range(len(q)+1) for s in combinations(q,k)):
                good.add(w)
        local.append((p,frozenset(v for v in words if all((t^v) in good for t in T))))
        if balanced:
            exact.append((p,frozenset(v for v in words if {t^v for t in T}==ag[p])))
    return local, exact if balanced else None


def _scatter(p,w):
    return sum(1<<j for i,j in enumerate(p) if w>>i&1)


@lru_cache(maxsize=512)
def _normal(w,allowed):
    """For a nonempty local truth set return its affine-hull equations."""
    first=min(allowed)
    return tuple((v,(first&v).bit_count()%2) for v in range(1,1<<w)
                 if all(((t^first)&v).bit_count()%2==0 for t in allowed))


def _affine(w,s):
    return bool(s) and len(s)*(len(_normal(w,s))+1)==1<<w


@lru_cache(maxsize=512)
def _inner(w,s,prefer_one):
    if _affine(w,s):return s
    order=sorted(s,reverse=prefer_one)
    for k in (4,2,1):  # largest admissible proper affine flat in <=3 bits
        for t in combinations(order,k):
            h=frozenset(t)
            if _affine(w,h):return h
    raise AssertionError("Expected a nonempty allowed set.")


def _linear(local):
    piv={}
    for p,s in local:
        if not s:return None
        for v,b in _normal(len(p),s):
            a=_scatter(p,v)
            while a:
                i=a.bit_length()-1
                if i not in piv:
                    piv[i]=a,b;break
                r,c=piv[i];a^=r;b^=c
            else:
                if b:return None
    x=0
    for i,(row,b) in sorted(piv.items()):
        if (row&x).bit_count()%2!=b:x|=1<<i
    return x


def _satisfies(local,x):
    return all(sum(1<<i for i,j in enumerate(p) if x>>j&1) in s for p,s in local)


def _bijunctive(n,local):
    clauses=[]
    for p,s in local:
        width=len(p);forb=set()
        for m in range(1,1<<width):
            if m.bit_count()>2:continue
            realized={w&m for w in s}
            for v in range(1<<width):
                if v&m!=v or v in realized:continue
                forb.update(w for w in range(1<<width) if w&m==v)
                clauses.append(tuple((j,v>>i&1) for i,j in enumerate(p) if m>>i&1))
        if len(s)+len(forb)!=1<<width:return None
    return _solve_binary_forbidden_patterns(n,clauses)


def _horn(local,dual):
    h=[]
    for p,s in local:
        full=(1<<len(p))-1
        t={full^v for v in s} if dual else s
        if any((a&b) not in t for a in t for b in t):return None
        h.append((p,t))
    x=0;allbits=0
    for p,_ in h:allbits|=_scatter(p,(1<<len(p))-1)
    while True:
        old=x
        for p,t in h:
            lower=sum(1<<i for i,j in enumerate(p) if x>>j&1)
            compatible=[v for v in t if v&lower==lower]
            if not compatible:return None
            m=compatible[0]
            for v in compatible[1:]:m &= v
            x |= _scatter(p,m)
        if x==old:return x^allbits if dual else x


def _flips(n,a,b):
    local,exact=_local(a,b)
    if any(not s for _,s in local):return None
    def make(x,method):
        return _pack((-(i+1) if x>>i&1 else i+1 for i in range(n)),method)
    if exact is not None:
        # Each nonempty same-size equality set is a coset of a stabilizer.
        x=_linear(exact)
        if x is not None and _satisfies(exact,x):return make(x,"translate-equality")
    x=_linear(local)
    if x is None:return None   # even affine hulls inconsistent
    if _satisfies(local,x):return make(x,"translate-affine")
    for name,fn in (("translate-2sat",lambda:_bijunctive(n,local)),
                    ("translate-horn",lambda:_horn(local,False)),
                    ("translate-dual-horn",lambda:_horn(local,True))):
        x=fn()
        if x is not None:return make(x,name)
    for preferred in (False,True):
        x=_linear([(p,_inner(len(p),s,preferred)) for p,s in local])
        if x is not None:return make(x,"translate-inner")
    return None


def find_flip_transport(n,source,target):
    """Find a certified diagonal sign flip. No global 2^n flip enumeration.

    Complete for canonical same-support sign-pattern translation, or when the
    local subsumption-admissible sets are all affine, all bijunctive, all
    Horn, or all dual-Horn. No completeness promise for arbitrary 3-CNFs.
    """
    a,b=_raw(n,source),_raw(n,target)
    c=_flips(n,canonical_cnf(n,a,3),canonical_cnf(n,b,3))
    if c is not None and not check_transport(n,a,b,c):raise AssertionError("Invalid shift")
    return c


def _rename(n,a,b):
    """One candidate from joint color refinement, not complete isomorphism."""
    if sorted(map(len,a))!=sorted(map(len,b)):return None
    def graph(f,off):
        adj=[[off+(i^1)] for i in range(2*n)]+[[] for _ in f]
        for i,c in enumerate(f):
            for lit in c:
                v=2*(abs(lit)-1)+int(lit<0)
                adj[v].append(off+2*n+i);adj[2*n+i].append(off+v)
        return adj
    off=2*n+len(a)
    adj=graph(a,0)+graph(b,off)
    colors=([0]*(2*n)+[1]*len(a))*2
    while colors:
        palette={}
        nextcol=[]
        for v,neighbors in enumerate(adj):
            sig=(colors[v],tuple(sorted(colors[w] for w in neighbors)))
            nextcol.append(palette.setdefault(sig,len(palette)))
        stable=len(palette)==len(set(colors))
        colors=nextcol
        if stable:break
    def groups(o):
        res=defaultdict(list)
        for i in range(n):res[tuple(sorted(colors[o+2*i:o+2*i+2]))].append(i)
        return res
    src,tgt=groups(0),groups(off)
    if src.keys()!=tgt.keys() or any(len(src[k])!=len(tgt[k]) for k in tgt):return None
    out=[0]*n
    for k,inds in tgt.items():
        both=set(inds)&set(src[k])
        pairs=[(j,j) for j in both]+list(zip((j for j in inds if j not in both),
                                             (j for j in src[k] if j not in both)))
        for j,i in pairs:
            out[j]=i+1 if colors[off+2*j]==colors[2*i] else -(i+1)
    return _pack(out,"refined-renaming")


def _single(n,a,b):
    """Complete for substitutions differing from identity on at most one image."""
    aset=set(frozenset(c) for c in a)
    def syntactic(row):
        return any(frozenset(s) in aset for j in range(len(row)+1) for s in combinations(row,j))
    failed=[c for c in b if not syntactic(c)]
    ident=list(range(1,n+1))
    if not failed:return _pack(ident,"identity")
    eligible=set.intersection(*(set(map(abs,c)) for c in failed))
    for v in sorted(eligible):
        affected=[c for c in b if v in c or -v in c]
        for value in [False,True,*range(1,n+1),*range(-1,-n-1,-1)]:
            if type(value) is int and value==v:continue
            for c in affected:
                pos=v in c
                tail=set(c)-{v,-v}
                if type(value) is bool:
                    if value==pos:continue
                else:
                    mapped=value if pos else -value
                    if -mapped in tail:continue
                    tail.add(mapped)
                if not syntactic(tail):break
            else:
                images=ident.copy();images[v-1]=value
                return _pack(images,"single-substitution")
    return None


# 'single' includes signed many-to-one folds and a single constant.
STRATEGIES=("identity","flip","rename","single","constants")


def find_transport(n, source, target, *, strategies=STRATEGIES):
    """Find a checked A->B substitution in deterministic polynomial time.

    This is not complete. Color refinement only proposes a checked candidate;
    arbitrary signed-permutation or endomorphism search is not enumerated.
    Input size includes n (an explicitly listed variable scope). Strategies
    can be selected to distinguish sign shifts, genuine one-way subsumption,
    renamings and constant SAT witnesses when measuring pruning.
    """
    raw_a,raw_b=_raw(n,source),_raw(n,target)
    a,b=canonical_cnf(n,raw_a,3),canonical_cnf(n,raw_b,3)
    if isinstance(strategies,str):raise ValueError("strategies must be a sequence of method names")
    methods=tuple(strategies)
    if any(s not in STRATEGIES for s in methods):raise ValueError("unknown strategy")
    for s in methods:
        if s=="identity":c=_pack(range(1,n+1),"identity")
        elif s=="flip":c=_flips(n,a,b)
        elif s=="rename":c=_rename(n,a,b)
        elif s=="single":c=_single(n,a,b)
        else:
            for bit in (False,True):
                c=_pack([bit]*n,"constant-word")
                if check_transport(n,raw_a,raw_b,c):return c
            continue
        if c is not None and check_transport(n,raw_a,raw_b,c):return c
    return None
