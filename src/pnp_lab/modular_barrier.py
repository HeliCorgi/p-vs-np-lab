"""Hall/forest certificates that proper-3-CNF fragments have full affine hull over any field."""

from collections import defaultdict, deque
import random


def _proper(n, clauses):
    if type(n) is not int or n < 0:
        raise ValueError("expected nonnegative variable count")
    rows = tuple(tuple(c) for c in clauses)
    if any(len(c) != 3 or len({abs(l) for l in c}) != 3 or
           any(type(l) is not int or not 0 < abs(l) <= n for l in c) for c in rows):
        raise ValueError("expected three different named variables per clause")
    return rows


def satisfies(clauses, x):
    return all(any(bool(x >> (abs(l)-1) & 1) == (l>0) for l in c) for c in clauses)


def hall_free_cube(n, clauses, axes):
    """Fix all other bits so every setting on specified axes is a model.

    Matching is sufficient, not necessary. Return the base word (axes zero).
    """
    rows = _proper(n, clauses)
    axes=frozenset(axes)
    if any(type(axis) is not int or not 1<=axis<=n for axis in axes):
        raise ValueError("axes are one-based variables")
    owner={}; chosen={}
    for start in range(len(rows)):
        # Alternating paths: left = clauses, right = variables. Exclude axis.
        pred={start:None};queue=deque([start]);end=None
        while queue and end is None:
            i=queue.popleft()
            for l in rows[i]:
                v=abs(l)
                if v in axes:continue
                if v not in owner:
                    end=(i,l);break
                h=owner[v]
                if h not in pred:
                    pred[h]=(i,l);queue.append(h)
        if end is None:return None
        while end is not None:
            i,l=end;owner[abs(l)]=i;chosen[i]=l;end=pred[i]
    word=sum(1<<(l-1) for l in chosen.values() if l>0)
    return word


def forest_ball(n,clauses):
    """Return a center whose whole radius-one Hamming ball consists of models."""
    rows=_proper(n,clauses)
    var=defaultdict(list)
    for i,c in enumerate(rows):
        for l in c:var[abs(l)].append(i)
    seen=set();fseen=set();word=0
    for root in sorted(var):
        if root in seen:continue
        q=[root];seen.add(root)
        while q:
            v=q.pop()
            for i in var[v]:
                if i in fseen:continue
                fseen.add(i)
                for l in rows[i]:
                    w=abs(l)
                    if w==v:continue
                    if w in seen:return None
                    seen.add(w);q.append(w)
                    if l>0:word|=1<<(w-1)
    return word


def incidence_girth(n,clauses):
    """Shortest simple cycle length in the bipartite variable-clause graph, or None."""
    rows=_proper(n,clauses);adj=defaultdict(list)
    for i,c in enumerate(rows):
        a=n+i+1
        for l in c:
            v=abs(l);adj[v].append(a);adj[a].append(v)
    shortest=None
    for root in adj:
        dist={root:0};parent={root:None};queue=deque([root])
        while queue:
            u=queue.popleft()
            if shortest is not None and dist[u]*2>=shortest:continue
            for v in adj[u]:
                if v not in dist:
                    parent[v]=u;dist[v]=dist[u]+1;queue.append(v)
                elif parent[u]!=v and parent[v]!=u:
                    length=dist[v]+dist[u]+1
                    shortest=length if shortest is None else min(shortest,length)
    return shortest


def line_fixture(seed=0):
    """One proper clause on each projective line in F2^5. No paired NAE clauses."""
    rng=random.Random(seed)
    lines=[(a,b,a^b) for a in range(1,32) for b in range(a+1,32) if b<a^b]
    rng.shuffle(lines)
    return 31,tuple(tuple(v if rng.getrandbits(1) else -v for v in line) for line in lines)


def raw_search(rows):
    """Small-instance decision tree. Leaves name a raw falsified clause; no propagation oracle."""
    def run(cs,values):
        if not cs:
            return sum(1<<(v-1) for v,b in values.items() if b),None
        i,c=min(cs,key=lambda u:len(u[1]))
        if not c:return None,i
        pivot=abs(c[0]);children=[]
        for val in (False,True):
            tr=pivot if val else -pivot
            left=[(j,tuple(x for x in d if x!=-tr)) for j,d in cs if tr not in d]
            word,tree=run(left,{**values,pivot:val})
            if word is not None:return word,None
            children.append(tree)
        return None,(pivot,*children)
    return run(list(enumerate(rows)),{})


def check_tree(n,clauses,tree):
    rows=_proper(n,clauses)
    def check(t,values):
        if type(t) is int:
            return 0<=t<len(rows) and all(abs(l) in values and values[abs(l)]!=(l>0) for l in rows[t])
        if not isinstance(t,(list,tuple)) or len(t)!=3:return False
        v,a,b=t
        return type(v) is int and 1<=v<=n and v not in values and check(a,{**values,v:False}) and check(b,{**values,v:True})
    return check(tree,{})


def preorder(tree):
    """Negative tokens split on their absolute variable; nonnegative tokens cite clauses."""
    if type(tree) is int:return [tree]
    v,a,b=tree
    return [-v]+preorder(a)+preorder(b)


def check_preorder(n,clauses,certificate):
    rows=_proper(n,clauses);todo=[{}]
    if not isinstance(certificate,(list,tuple)):return False
    for token in certificate:
        if not todo or type(token) is not int:return False
        values=todo.pop()
        if token>=0:
            if token>=len(rows) or not all(abs(l) in values and values[abs(l)]!=(l>0) for l in rows[token]):
                return False
        else:
            v=-token
            if v>n or v in values:return False
            todo.extend(({**values,v:True},{**values,v:False}))
    return not todo


def stretched_image(n,source,k,pin_n,pin_cnf,false_literal):
    """Conditional construction using a supplied pin: pin_cnf is SAT and entails ¬false_literal.

    The caller supplies this semantic premise. Every attached copy is private.
    The returned maps are for experiment-level witness lifting, not a solver.
    """
    source=_proper(n,source);pin_cnf=_proper(pin_n,pin_cnf)
    if type(k) is not int or k<1 or type(false_literal) is not int or not 1<=abs(false_literal)<=pin_n:
        raise ValueError("bad stretch or pin")
    fresh=0;rows=[];uses=defaultdict(list);copies={};starts=[]
    for c in source:
        acc=[]
        for l in c:
            fresh+=1;uses[abs(l)].append(fresh);copies[fresh]=abs(l);acc.append(fresh if l>0 else -fresh)
        rows.append(tuple(acc))
    edges=[]
    for v,ends in uses.items():
        if len(ends)<2:continue
        for j,a in enumerate(ends):
            for _ in range(k-1):
                fresh+=1;copies[fresh]=v;edges.append((a,fresh));a=fresh
            edges.append((a,ends[(j+1)%len(ends)]))
    for a,b in edges:
        base=fresh;fresh+=pin_n;starts.append(base)
        def remap(l):return (base+abs(l))*(1 if l>0 else -1)
        rows.append((-a,b,remap(false_literal)))
        rows.extend(tuple(remap(l) for l in c) for c in pin_cnf)
    return fresh,tuple(rows),copies,tuple(starts)


def lift_stretched(source_word,pin_word,copies,starts):
    return sum(1<<(v-1) for v,old in copies.items() if source_word>>(old-1)&1) | sum(pin_word<<s for s in starts)
