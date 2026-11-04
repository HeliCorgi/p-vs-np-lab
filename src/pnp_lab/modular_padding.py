"""Eliminate private signed pivots successively, then replay a local field refutation."""
from collections import defaultdict,Counter
from heapq import heapify, heappop, heappush

from .modular_hull import modular_hull_refute,check_modular_hull

KIND='private-peel-modular-v1'


def _inputs(n,clauses):
    if type(n) is not int or n<0 or isinstance(clauses,(str,bytes)):raise ValueError('invalid scope/source')
    result=[]
    for c in clauses:
        if isinstance(c,(str,bytes)):raise ValueError('invalid row')
        c=tuple(c)
        if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):raise ValueError('invalid width or literal')
        result.append(tuple(sorted(set(c),key=lambda l:(abs(l),l))))
    return tuple(result)


def _taut(row):
    return any(-l in row for l in row)


def private_chain(n,clauses,*,length=10):
    """Replace each proper original clause L OR b with length fresh bits.
    A complete chain of binary implications connects its two ends.
    """
    if type(length) is not int or length<1:raise ValueError('positive chain length required')
    cs=_inputs(n,clauses);rows=[]
    for c in cs:
        if not 2<=len(c)<=3 or _taut(c):raise ValueError('expected proper clauses of width two or three')
        start=n+1;n+=length
        rows.append((*c[:-1],start))
        rows.extend((-i,i+1) for i in range(start,n))
        rows.append((-n,c[-1]))
    return n,tuple(rows)


def plant_chain_model(n,clauses,word,*,length=10):
    cs=_inputs(n,clauses)
    if type(word) is not int or word<0 or word.bit_length()>n:raise ValueError('invalid word')
    if type(length) is not int or length<1:raise ValueError('positive chain length required')
    mask=word
    for c in cs:
        if not 2<=len(c)<=3 or _taut(c) or not any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c):
            raise ValueError('not a satisfying word of the promised base CNF')
        b=c[-1]
        if bool(word>>(abs(b)-1)&1)==(b>0):mask|=((1<<length)-1)<<n
        n+=length
    return mask


def peel(n,clauses):
    """Return (residual CNF on original names, step list). No generator metadata."""
    raw=_inputs(n,clauses);rows={i:c for i,c in enumerate(raw) if not _taut(c)}
    occ=defaultdict(set)
    for i,c in rows.items():
        for l in c:occ[l].add(i)
    def eligible(x):
        return len(occ[x])==len(occ[-x])==1
    heap=[x for x in list(occ) if x>0 and eligible(x)]
    heapify(heap);steps=[]
    while heap:
        v=heappop(heap)
        if not eligible(v):continue
        i=next(iter(occ[v]));j=next(iter(occ[-v]))
        a,b=rows[i],rows[j]
        res=tuple(sorted((set(a)|set(b))-{v,-v},key=lambda l:(abs(l),l)))
        taut=_taut(res)
        if len(res)>3 and not taut:continue
        new_id=len(raw)+len(steps)
        steps.append([v,i,j])
        for old_index,old in ((i,a),(j,b)):
            rows.pop(old_index)
            for l in old:occ[l].remove(old_index)
        if not taut:
            rows[new_id]=res
            for l in res:occ[l].add(new_id)
        for x in {abs(l) for l in a+b}:
            if eligible(x):heappush(heap,x)
    return tuple(rows[i] for i in sorted(rows)),steps


def _replay(n,clauses,steps,*,want_history=False):
    # Unlike discovery this replayer sees only proposed parent IDs. It never
    # searches for a pivot or depends on the finder's heap/order.
    src=_inputs(n,clauses)
    if not isinstance(steps,(list,tuple)) or len(steps)>n:raise ValueError('bad step count')
    active={i:frozenset(c) for i,c in enumerate(src) if not _taut(c)}
    occ=Counter(l for c in active.values() for l in c);history=[]
    for t,entry in enumerate(steps):
        if not isinstance(entry,(tuple,list)) or len(entry)!=3 or any(type(z) is not int for z in entry):
            raise ValueError('bad step')
        v,i,j=entry
        if not 1<=v<=n or i==j or i not in active or j not in active or occ[v]!=1 or occ[-v]!=1:
            raise ValueError('parents not private')
        a,b=active[i],active[j]
        if v not in a or -v not in b:raise ValueError('wrong resolution signs')
        left,right=a-{v},b-{-v}
        r=left|right
        taut=any(-l in r for l in r)
        if not taut and len(r)>3:raise ValueError('wide resolvent')
        if want_history:history.append((v,left))
        del active[i],active[j]
        occ.subtract(a);occ.subtract(b)
        if not taut:active[len(src)+t]=r;occ.update(r)
    rows=tuple(tuple(sorted(active[i],key=lambda l:(abs(l),l))) for i in sorted(active))
    return rows,history


def lift_after_peeling(n,clauses,steps,residual_word):
    cs=_inputs(n,clauses);rows,hist=_replay(n,cs,steps,want_history=True)
    if type(residual_word) is not int or residual_word<0 or residual_word.bit_length()>n:
        raise ValueError('invalid residual word')
    x=residual_word
    def holds(c):
        return any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c)
    if not all(holds(c) for c in rows):raise ValueError('residual word falsifies a row')
    for v,left in reversed(hist):
        if holds(left):x &= ~(1<<(v-1))
        else:x |= 1<<(v-1)
    if not all(holds(c) for c in cs):raise AssertionError('invalid recovered witness')
    return x


def check_peeled_modular(n,clauses,cert):
    try:
        if not isinstance(cert,dict) or cert.get('kind')!=KIND:return False
        rows,_=_replay(n,clauses,cert['steps'])
        return check_modular_hull(n,rows,cert['inner'])
    except (ValueError,IndexError,TypeError,KeyError,AttributeError):return False


def peeled_modular_refute(n,clauses,*,prime=3,max_scopes=None):
    raw=_inputs(n,clauses)
    rows,steps=peel(n,raw)
    inner=modular_hull_refute(n,rows,prime=prime,max_scopes=max_scopes)
    stats=dict(steps=len(steps),residual_clauses=len(rows),residual_active_variables=len({abs(l) for c in rows for l in c}),
               modular=inner['stats'])
    if inner['status']!='UNSAT':return dict(status='UNKNOWN',certificate=None,stats=stats)
    cert=dict(kind=KIND,steps=steps,inner=inner['certificate'])
    if not check_peeled_modular(n,raw,cert):raise AssertionError('invalid composed proof')
    return dict(status='UNSAT',certificate=cert,stats=stats)


def shield_equalities(n,clauses,word=None):
    """Conservative extension. Each coordinate and its two aliases have 2+ occurrences per sign."""
    cs=list(_inputs(n,clauses))
    if word is not None and (type(word) is not int or word<0 or word.bit_length()>n):
        raise ValueError('invalid assignment')
    for v in range(1,n+1):
        triple=(v,n+2*v-1,n+2*v)
        cs.extend((-a,b) for a in triple for b in triple if a!=b)
    y=word
    if y is not None:
        for v in range(1,n+1):
            if (word>>(v-1))&1:y|=3<<(n+2*(v-1))
    return 3*n,tuple(cs),y
