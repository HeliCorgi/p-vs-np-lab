"""Proof-producing preprocessing for the old simple-support blind image.

Detect small local forced cubes, then quotient signed binary implications.
No input coordinates, seeds or constructor correspondences are supplied.
"""

from collections import Counter, defaultdict, deque
from itertools import combinations
from .private_resolution import _input


def _shape(c):
    return tuple(sorted(set(c), key=lambda l: (abs(l),l)))


def _taut(c):
    return any(-l in c for l in c)


def _satisfies(rows, x):
    return all(any(bool((x>>(abs(l)-1)) & 1)==(l>0) for l in row) for row in rows)


def _scopes(cs):
    hood=defaultdict(set); triples=defaultdict(list)
    for i,row in enumerate(cs):
        vs=tuple(sorted(set(map(abs,row))))
        for v in vs:hood[v].update(vs)
        if len(vs)==3 and not _taut(row):triples[vs].append(i)
    pools={tuple(sorted(h)) for h in hood.values() if len(h)==6}
    for vs in sorted(pools):
        deg=Counter(); ids=[]
        for tri in combinations(vs,3):
            if tri in triples:
                deg.update(tri);ids.extend(triples[tri])
        if len(deg)==6 and min(deg.values())>=2 and sum(d>=4 for d in deg.values())>=5:
            yield vs,sorted(ids)


def _local(n,cs,pack):
    vs,ids=pack['scope'],pack['clauses']
    if (not isinstance(vs,list) or not 0<len(vs)<=6 or any(type(v) is not int or not 1<=v<=n for v in vs) or
        vs!=sorted(set(vs)) or not isinstance(ids,list) or not ids or
        any(type(i) is not int or not 0<=i<len(cs) for i in ids)):
        raise ValueError('invalid local proof')
    slots={v:i+1 for i,v in enumerate(vs)}
    if any(abs(l) not in slots for i in ids for l in cs[i]):raise ValueError('outside local scope')
    rows=[tuple(slots[abs(l)]*(1 if l>0 else -1) for l in cs[i]) for i in ids]
    words=[x for x in range(1<<len(vs)) if _satisfies(rows,x)]
    if not words:return None
    return {v:bool(words[0]>>i&1) for i,v in enumerate(vs)
            if all(((x^words[0])>>i&1)==0 for x in words)}


def _pins(n,cs,packs):
    if not isinstance(packs,list):raise ValueError('invalid collection')
    pins={}
    for p in packs:
        local=_local(n,cs,p)
        if local is None or any(i in pins and pins[i]!=v for i,v in local.items()):return None
        pins.update(local)
    return pins


def _at(c,mp):
    rem=[]
    for l in c:
        a=mp.get(abs(l),abs(l))
        if type(a) is bool:
            if a==(l>0):return None
        else:rem.append(a if l>0 else -a)
    t=_shape(rem)
    return None if _taut(t) else t


def _graph(rows):
    g=defaultdict(list);b=defaultdict(list);used=set()
    for i,c in enumerate(rows):
        if c is None or not 1<=len(c)<=2:continue
        a=c[0];d=c[-1]
        for u,v in {(-a,d),(-d,a)}:
            g[u].append((v,i));b[v].append((u,i));used.update((u,v))
    return g,b,used


def _components(g,b,vertices):
    order=[];seen=set()
    for v in sorted(vertices):
        if v in seen:continue
        seen.add(v)
        stack=[(v,iter(g[v]))]
        while stack:
            a,it=stack[-1]
            for t,_ in it:
                if t not in seen:seen.add(t);stack.append((t,iter(g[t])));break
            else:order.append(a);stack.pop()
    seen=set()
    for v in reversed(order):
        if v in seen:continue
        region={v};stack=[v];seen.add(v)
        while stack:
            a=stack.pop()
            for t,_ in b[a]:
                if t not in seen:seen.add(t);region.add(t);stack.append(t)
        yield region


def _tree(g,region,r):
    edges=[];seen={r};q=deque([r])
    while q:
        v=q.popleft()
        for w,i in g[v]:
            if w in region and w not in seen:
                seen.add(w);edges.append([v,w,i]);q.append(w)
    return edges


def _groups(rows):
    g,b,vs=_graph(rows);out=[]
    for c in _components(g,b,vs):
        if len(c)<2:continue
        r=min(map(abs,c))
        if r not in c:continue  # the complementary component represents the same equalities
        rec={'root':r,'out':_tree(g,c,r),'back':_tree(b,c,r)}
        out.append(rec)
        if -r in c:break
    return out


def _validate_trees(rows,groups,n,pins):
    if not isinstance(groups,list):raise ValueError('invalid collection')
    mp=dict(pins);used=set()
    for group in groups:
        root=group['root']
        if type(root) is not int or not 1<=root<=n:raise ValueError('invalid root')
        terms=[]
        for key in ('out','back'):
            seen={root}
            for e in group[key]:
                p,q,i=e
                if (any(type(j) is not int for j in (p,q,i)) or not 1<=abs(q)<=n or
                    p not in seen or q in seen or not 0<=i<len(rows)):raise ValueError('malformed tree')
                c=rows[i]
                if not c or len(c)>2:raise ValueError('no binary implication')
                a,b=(p,q) if key=='out' else (q,p)
                if (a,b) not in ((-c[0],c[-1]),(-c[-1],c[0])):raise ValueError('invalid edge')
                seen.add(q)
            terms.append(seen)
        if terms[0]!=terms[1] or len(terms[0])<2:raise ValueError('incomplete tree')
        literals=terms[0]; ids={abs(l) for l in literals}
        if ids.intersection(pins) or ids.intersection(used):raise ValueError('overlapping proof')
        if len(ids)!=len(literals):return None
        used.update(ids);mp.update({abs(l):root if l>0 else -root for l in literals})
    return mp


def _empty():
    return {'status':'UNSAT','n_reduced':0,'clauses':[[]],'images':[]}


_UNSET=object()


def _result(n,cs,cert,pins=_UNSET):
    """Replay small truth tables and signed implication trees, not the search."""
    if cert['kind']!='blind-cube-scc-v1':raise ValueError('incorrect proof kind')
    if pins is _UNSET:pins=_pins(n,cs,cert['packs'])
    if pins is None:return _empty()
    rows=[_at(c,pins) for c in cs]
    if () in rows:return _empty()
    mp=_validate_trees(rows,cert['groups'],n,pins)
    if mp is None:return _empty()
    fs={d for c in cs if (d:=_at(c,mp)) is not None}
    if () in fs:return _empty()
    counts=Counter(abs(l) for d in fs for l in d)
    # A single isolated binary clause always has a satisfying extension.
    private={}
    for c in fs:
        if len(c)==2 and all(counts[abs(l)]==1 for l in c):
            private.update({abs(l):l>0 for l in c})
    reduced={d for c in fs if (d:=_at(c,private)) is not None}
    active=sorted({abs(l) for c in reduced for l in c}); idx={v:i+1 for i,v in enumerate(active)}
    out=sorted(_shape(idx[abs(l)]*(1 if l>0 else -1) for l in c) for c in reduced)
    imgs=[]
    for v in range(1,n+1):
        a=mp.get(v,v)
        if type(a) is bool:imgs.append(a)
        elif abs(a) in idx:imgs.append(idx[abs(a)]*(1 if a>0 else -1))
        else:imgs.append(private.get(abs(a),False)==(a>0))
    return dict(status='OPEN' if out else 'SAT',n_reduced=len(active),clauses=[list(c) for c in out],images=imgs)


def _equal(x,y):
    if type(x) is not type(y):return False
    if isinstance(x,list):return len(x)==len(y) and all(_equal(a,b) for a,b in zip(x,y))
    return x==y


def check_recovery(n,clauses,result):
    """Check both projection/lift semantics by replaying the local certificate."""
    try:
        cs=_input(n,clauses); expected=_result(n,cs,result['certificate'])
        return all(_equal(result[k],v) for k,v in expected.items())
    except (KeyError,ValueError,IndexError,TypeError,AttributeError,OverflowError):return False


def recover_blind(n,clauses):
    """Return certified equisatisfiable compact CNF. OPEN does not settle SAT."""
    cs=_input(n,clauses)
    packs=[{'scope':list(vs),'clauses':ii} for vs,ii in _scopes(cs)]
    pin=_pins(n,cs,packs)
    rows=[_at(c,pin) for c in cs] if pin is not None else []
    groups=[] if pin is None or () in rows else _groups(rows)
    cert=dict(kind='blind-cube-scc-v1',packs=packs,groups=groups)
    ans=_result(n,cs,cert,pins=pin);ans['certificate']=cert
    ans['stats']=dict(packs=len(packs),truth_assignments_tested=sum(1<<len(p['scope']) for p in packs),
                      forced_pins=None if pin is None else len(pin),signed_components=len(groups),
                      tree_edges=sum(len(g['out'])+len(g['back']) for g in groups))
    return ans


def lift_recovered_model(n,clauses,result,mask):
    cs=_input(n,clauses)
    if not check_recovery(n,cs,result) or result['status']=='UNSAT':raise ValueError('invalid reduction')
    if type(mask) is not int or mask<0 or mask.bit_length()>result['n_reduced'] or not _satisfies(result['clauses'],mask):
        raise ValueError('invalid reduced model')
    word=sum(1<<j for j,a in enumerate(result['images'])
             if (a if type(a) is bool else bool(mask>>(abs(a)-1)&1)==(a>0)))
    if not _satisfies(cs,word):raise AssertionError('invalid lift into original CNF')
    return word
