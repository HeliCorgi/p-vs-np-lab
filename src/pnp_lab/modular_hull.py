"""Checked local affine consequences of a raw Boolean 3-CNF over GF(2) or GF(3).

Variables are always Boolean, even inside a local GF(3) truth table. A
consistent relaxation returns UNKNOWN. The trust boundary is the independent
original-clause truth-table and modular-sum checker.
"""
from collections import defaultdict
from itertools import combinations, product
from functools import lru_cache

MAX_SCOPE = 9
KIND = 'boolean-modular-hull-v1'


def _input(n, clauses):
    if type(n) is not int or n < 0 or isinstance(clauses,(str,bytes)):
        raise ValueError('invalid scope or clauses')
    cs=[]
    try:
        for row in clauses:
            if isinstance(row,(str,bytes)):
                raise ValueError('invalid clause')
            row=tuple(row)
            if len(row)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in row):
                raise ValueError('invalid literal or width')
            cs.append(row)
    except TypeError as exc:
        raise ValueError('invalid clause sequence') from exc
    return tuple(cs)


def _index(cs):
    # Repeated equivalent original clauses are unnecessary as local evidence.
    idx=defaultdict(dict)
    for i,c in enumerate(cs):
        s=frozenset(c)
        if any(-l in s for l in s):continue
        idx[tuple(sorted(map(abs,s)))].setdefault(tuple(sorted(s,key=abs)), i)
    return idx


def _scopes(idx):
    blocks=defaultdict(list)
    for s in idx:
        if len(s)==3 and all(p in idx for p in combinations(s,2)):
            for v in s:blocks[v].append(s)
    nbr=defaultdict(set)
    scopes=set(idx)
    for s in idx:
        for v in s:nbr[v].update(s)
        # Always an all-original-scope option; block expansion may also
        # enlarge a subset of variables (important for mixed encodings).
        for bs in product(*(((v,),*blocks[v]) for v in s)):
            u=tuple(sorted(set().union(*bs)))
            if len(u)<=MAX_SCOPE:scopes.add(u)
    scopes.update(tuple(sorted(s)) for s in nbr.values() if len(s)<=MAX_SCOPE)
    return sorted(scopes,key=lambda s:(len(s),s))


def discover_scopes(n, clauses):
    return _scopes(_index(_input(n,clauses)))


@lru_cache(maxsize=MAX_SCOPE+1)
def _columns(w):
    return tuple(sum(1<<x for x in range(1<<w) if x>>j&1) for j in range(w))


def _local(idx,s):
    pos={v:i for i,v in enumerate(s)}
    full=(1<<(1<<len(s)))-1; words=full; cols=_columns(len(s));ids=[]
    for j in range(min(3,len(s))+1):
        for t in combinations(s,j):
            for c,ix in idx.get(t,{}).items():
                ok=0
                for l in c:
                    col=cols[pos[abs(l)]];ok |= col if l>0 else full^col
                words &= ok;ids.append(ix)
    return words,ids


def _annihilator(words,d,p):
    # Right nullspace of rows (x_1,...,x_d,1), x a local model.
    # To refute a locally empty formula we only need the equation 0=1.
    if not words:return [(0,)*d+(1,)]
    piv={}
    while words:
        b=words&-words;words-=b;v=b.bit_length()-1
        a=[(v>>j)&1 for j in range(d)]+[1]
        for j in range(d+1):
            if not a[j]:continue
            if j not in piv:
                k=pow(a[j],-1,p);piv[j]=[(k*x)%p for x in a];break
            k=a[j];r=piv[j]
            for h in range(j,d+1):a[h]=(a[h]-k*r[h])%p
        if len(piv)==d+1:return []
    null=[]
    for free in range(d+1):
        if free in piv:continue
        y=[0]*(d+1);y[free]=1
        for j in sorted(piv,reverse=True):
            y[j]=-sum(a*v for a,v in zip(piv[j][j+1:],y[j+1:]))%p
        null.append(tuple(y[:-1])+((-y[-1])%p,))
    return null


def _sub(row,k,other,p):
    for j,v in other.items():
        w=(row.get(j,0)-k*v)%p
        if w:row[j]=w
        else:row.pop(j,None)


def _scale(row,k,p):
    return {i:(v*k)%p for i,v in row.items()}


def _row_holds(n,cs,p,t):
    vs=t['scope'];coeff=t['coeff'];b=t['rhs'];ids=t['clauses']
    if (type(vs) not in (list,tuple) or len(vs)>MAX_SCOPE
        or any(type(v) is not int or not 1<=v<=n for v in vs) or len(set(vs))!=len(vs)
        or type(coeff) not in (list,tuple) or len(coeff)!=len(vs)
        or any(type(a) is not int or not 0<=a<p for a in coeff)
        or type(b) is not int or not 0<=b<p or type(ids) not in (list,tuple) or not ids):return False
    if any(type(i) is not int or not 0<=i<len(cs) for i in ids):return False
    slot={v:i for i,v in enumerate(vs)};projected=[]
    for ix in ids:
        if any(abs(l) not in slot for l in cs[ix]):return False
        projected.append(tuple((slot[abs(l)],l>0) for l in cs[ix]))
    for x in range(1<<len(vs)):
        if sum(a for j,a in enumerate(coeff) if x>>j&1)%p==b:continue
        if all(any(((x>>j)&1)==sign for j,sign in row) for row in projected):return False
    return True


def check_modular_row(n,clauses,prime,term):
    """Check one affine consequence over Boolean points using only cited raw clauses."""
    try:
        return type(prime) is int and prime in (2,3) and _row_holds(n,_input(n,clauses),prime,term)
    except (AttributeError,TypeError,IndexError,KeyError,ValueError):
        return False


def check_modular_hull(n, clauses, cert):
    """No discovery, Gaussian elimination or local Boolean bitset code is used."""
    try:
        cs=_input(n,clauses)
        if type(cert) is not dict or cert.get('kind')!=KIND:return False
        p=cert['prime'];ts=cert['terms']
        if type(p) is not int or p not in (2,3) or type(ts) is not list or not ts:return False
        total={};rhs=0
        for t in ts:
            if not _row_holds(n,cs,p,t):return False
            for v,a in zip(t['scope'],t['coeff']):total[v]=(total.get(v,0)+a)%p
            rhs=(rhs+t['rhs'])%p
        return not any(total.values()) and rhs==1
    except (AttributeError,TypeError,IndexError,KeyError,ValueError):
        return False


def _limits(prime,max_scopes):
    if type(prime) is not int or prime not in (2,3):raise ValueError('prime must be 2 or 3')
    if max_scopes is not None and (type(max_scopes) is not int or max_scopes<0):
        raise ValueError('invalid scope limit')


def _start(prime,scopes):
    return dict(prime=prime,scopes_available=len(scopes),scopes_examined=0,
                max_scope_size=0,local_rows=0,local_assignments=0,budget_limited=False)


def _local_rows(idx,scopes,prime,cap,stats):
    for s in scopes:
        if cap is not None and stats['scopes_examined']>=cap:
            stats['budget_limited']=True;break
        stats['scopes_examined']+=1;stats['max_scope_size']=max(stats['max_scope_size'],len(s))
        words,ids=_local(idx,s);stats['local_assignments']+=1<<len(s)
        for a in _annihilator(words,len(s),prime):
            stats['local_rows']+=1
            yield s,ids,a


def collect_modular_rows(n,clauses,*,prime=3,max_scopes=None):
    """Collect all explored local affine basis rows, without global elimination."""
    _limits(prime,max_scopes)
    idx=_index(_input(n,clauses));sc=_scopes(idx);stats=_start(prime,sc)
    rows=[dict(scope=list(s),clauses=cl,coeff=list(a[:-1]),rhs=a[-1])
          for s,cl,a in _local_rows(idx,sc,prime,max_scopes,stats)]
    return rows,stats


def modular_hull_refute(n, clauses, *, prime=3,max_scopes=None):
    """Return UNSAT with proof, or UNKNOWN; the cap charges local scopes examined."""
    cs=_input(n,clauses)
    _limits(prime,max_scopes)
    p=prime;idx=_index(cs);scopes=_scopes(idx);stats=_start(prime,scopes);stats['global_rank']=0
    piv={};kept=[]
    def result(ids):
        # Add contributions from the same local table, so that each scope
        # need only be checked once even if several basis rows were used.
        groups={}
        for i,k in sorted(ids.items()):
            s,cl,a=kept[i]
            if s not in groups:groups[s]=(cl,[0]*len(a))
            vals=groups[s][1]
            for j,c in enumerate(a):vals[j]=(vals[j]+k*c)%p
        terms=[dict(scope=list(s),clauses=cl,coeff=vals[:-1],rhs=vals[-1])
               for s,(cl,vals) in sorted(groups.items()) if any(vals)]
        cert=dict(kind=KIND,prime=p,terms=terms)
        if not check_modular_hull(n,cs,cert):raise AssertionError('invalid hull proof')
        return dict(status='UNSAT',certificate=cert,stats=stats)
    for s,cl,a in _local_rows(idx,scopes,p,max_scopes,stats):
        row={i:v for i,v in zip(s,a) if v};rhs=a[-1];ids={len(kept):1}
        while row:
            j=min(row);k=row[j]
            if j not in piv:
                u=pow(k,-1,p)
                piv[j]=(_scale(row,u,p),rhs*u%p,_scale(ids,u,p))
                kept.append((s,cl,a));stats['global_rank']+=1;break
            old,b,pf=piv[j]
            _sub(row,k,old,p);rhs=(rhs-k*b)%p;_sub(ids,k,pf,p)
        else:
            if rhs:
                kept.append((s,cl,a))
                return result(_scale(ids,pow(rhs,-1,p),p))
    return dict(status='UNKNOWN',certificate=None,stats=stats)
