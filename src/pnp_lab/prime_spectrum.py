"""Find all exceptional local characteristics for Boolean affine equations.

Discovery takes raw signed CNF. A nonzero maximal integer minor bounds the
possible primes; evaluating actual modular rank eliminates its false alarms.
A separate bordering-minor check binds a local witness to raw clauses.
"""
from functools import lru_cache
from math import gcd
from .modular_hull import MAX_SCOPE, _input, _index, _scopes, _local


def _words(bits):
    while bits:
        b=bits & -bits
        yield b.bit_length()-1
        bits-=b


def _vec(word,d):
    return [(word>>j)&1 for j in range(d)]+[1]


def _det(mat):
    """Fraction-free Bareiss determinant with row permutations; det(empty)=1."""
    if not mat:return 1
    a=[list(row) for row in mat];sign=1;old=1
    for k in range(len(a)-1):
        j=next((i for i in range(k,len(a)) if a[i][k]),None)
        if j is None:return 0
        if j!=k:a[k],a[j]=a[j],a[k];sign=-sign
        b=a[k][k]
        for i in range(k+1,len(a)):
            for j in range(k+1,len(a)):
                a[i][j]=(b*a[i][j]-a[i][k]*a[k][j])//old
        old=b
    return sign*a[-1][-1]


def _minor(d,ws,cols):
    return _det([[1 if c==d else (w>>c)&1 for c in cols] for w in ws])


def _factor(a):
    a=abs(a);fs=[];p=2
    while p*p<=a:
        if a%p==0:
            fs.append(p)
            while a%p==0:a//=p
        p=3 if p==2 else p+2
    if a>1:fs.append(a)
    return fs


def _basis(d,words,p):
    piv={};chosen=[]
    for word in _words(words):
        v=_vec(word,d)
        for col in sorted(piv):
            a=v[col]
            if not a:continue
            row=piv[col]
            if p:
                v=[(x-a*y)%p for x,y in zip(v,row)]
            else:
                v=[row[col]*x-a*y for x,y in zip(v,row)]
                g=gcd(*v)
                if g>1:v=[x//g for x in v]
        col=next((j for j,x in enumerate(v) if x),None)
        if col is None:continue
        if p:
            inv=pow(v[col],-1,p);v=[x*inv%p for x in v]
        piv[col]=v;chosen.append(word)
        if len(chosen)==d+1:break
    cols=sorted(piv)
    return dict(rank=len(cols),words=chosen,columns=cols,minor=_minor(d,chosen,cols))


def spectrum_table(d,words):
    """words is a bitset of satisfying local words: bit w denotes word w."""
    if type(d) is not int or not 0<=d<=MAX_SCOPE or type(words) is not int or not 0<=words<1<<(1<<d):
        raise ValueError('invalid Boolean word table')
    q=_basis(d,words,0)
    mp={str(p):_basis(d,words,p) for p in _factor(q['minor'])}
    return dict(kind='affine-prime-spectrum-v1',dimension=d,models=words.bit_count(),
                rational=q,modular=mp,
                exceptional_primes=[int(p) for p,r in mp.items() if r['rank']<q['rank']])


def _rank_witness(d,table,wit,p):
    """Independently bound rank above and below: do not rerun discovery elimination."""
    r=wit['rank'];ws=wit['words'];cols=wit['columns'];delta=wit['minor']
    if (type(r) is not int or not 0<=r<=d+1 or type(delta) is not int or
        not isinstance(ws,list) or not isinstance(cols,list) or len(ws)!=r or len(cols)!=r or
        any(type(w) is not int or not 0<=w<1<<d or not table>>w&1 for w in ws) or
        any(type(c) is not int or not 0<=c<=d for c in cols) or len(set(ws))!=r or len(set(cols))!=r):return False
    if delta!=_minor(d,ws,cols) or (delta%p if p else delta)==0:return False
    if r==d+1 or r==table.bit_count():return True
    for word in _words(table):
        if word in ws:continue
        for col in range(d+1):
            if col in cols:continue
            a=_minor(d,ws+[word],cols+[col])
            if (a%p if p else a)!=0:return False
    return True


def check_local_spectrum(n,clauses,scope,cert):
    """Read every original clause contained in this coordinate set and verify its spectrum."""
    try:
        cs=_input(n,clauses)
        if not isinstance(scope,(tuple,list)) or len(scope)>MAX_SCOPE or len(set(scope))!=len(scope) or any(type(v) is not int or not 1<=v<=n for v in scope):return False
        if not isinstance(cert,dict) or cert.get('kind')!='affine-prime-spectrum-v1':return False
        d=len(scope);pos={v:i for i,v in enumerate(scope)}
        local=[tuple((pos[abs(l)],l>0) for l in c) for c in cs if all(abs(l) in pos for l in c)]
        table=sum(1<<w for w in range(1<<d) if all(any(bool(w>>i&1)==b for i,b in c) for c in local))
        if type(cert['dimension']) is not int or cert['dimension']!=d or type(cert['models']) is not int or cert['models']!=table.bit_count():return False
        q=cert['rational']
        if not _rank_witness(d,table,q,0):return False
        mp=cert['modular'];fs=_factor(q['minor'])
        if type(mp) is not dict or set(mp)!={str(p) for p in fs}:return False
        if not all(_rank_witness(d,table,mp[str(p)],p) for p in fs):return False
        ans=cert['exceptional_primes']
        return isinstance(ans,list) and all(type(p) is int for p in ans) and ans==[p for p in fs if mp[str(p)]['rank']<q['rank']]
    except (TypeError,ValueError,KeyError,IndexError):return False


def discover_prime_spectrum(n,clauses,*,max_scopes=None):
    if max_scopes is not None and (type(max_scopes) is not int or max_scopes<0):
        raise ValueError('invalid scope cap')
    cs=_input(n,clauses);idx=_index(cs);scopes=_scopes(idx)
    selected=scopes if max_scopes is None else scopes[:max_scopes]
    # The cache never scales with input size and its profiles do not escape
    # except as immutable-by-convention, independent examples per call.
    local=lru_cache(maxsize=1024)(spectrum_table)
    count={};examples={};empty=0
    for s in selected:
        table,_=_local(idx,s);q=local(len(s),table)
        if not table:empty+=1
        for p in q['exceptional_primes']:
            count[str(p)]=count.get(str(p),0)+1
            if str(p) not in examples:
                if not check_local_spectrum(n,cs,s,q):raise AssertionError('local-rank witness failed')
                examples[str(p)]=dict(scope=list(s),profile=q)
    return dict(primes=sorted(map(int,count)),complete_for_scopes=len(selected)==len(scopes),
                scanned_scopes=len(selected),available_scopes=len(scopes),empty_scopes=empty,
                exceptional_scope_counts=count,examples=examples)
