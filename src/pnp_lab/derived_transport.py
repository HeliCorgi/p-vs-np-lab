"""Clause-by-clause transport checked by unit reasons and shallow case splits.

Coordinates are 1-based; false/true map entries are distinct from integer
literals. A proof cites the caller's ORIGINAL 0-based clause indices.
"""
from itertools import combinations, product

from .witness_transport import _flips, _raw


KIND = 'derived-transport-v1'


def _validate_limit(v):
    if v is not None and (type(v) is not int or v<0):
        raise ValueError('expected nonnegative budget or None')


def _validate_depth(d):
    if type(d) is not int or d not in (0,1,2,3):raise ValueError('depth must be 0..3')


def _images(n,images):
    if not isinstance(images,(tuple,list)) or len(images)!=n:return False
    return all(type(v) is bool or (type(v) is int and 1<=abs(v)<=n) for v in images)


def _pull(c,images):
    out=set()
    for l in c:
        v=images[abs(l)-1]
        if type(v) is bool:
            if v==(l>0):return None
        else:
            r=v if l>0 else -v
            if -r in out:return None
            out.add(r)
    return tuple(sorted(out,key=abs))


def apply_derived_transport(n,cert,source_mask):
    if (type(n) is not int or n<0 or not isinstance(cert,dict) or cert.get('kind')!=KIND or
        not _images(n,cert.get('images')) or type(source_mask) is not int or
        source_mask<0 or source_mask.bit_length()>n):raise ValueError('invalid certificate or model')
    return sum(1<<i for i,v in enumerate(cert['images']) if
               (v if type(v) is bool else bool(source_mask & 1<<(abs(v)-1))==(v>0)))


def _verify(cs,goal,proof,n):
    # Separate literal-set evaluator, not the finder's bit-mask propagation.
    if not isinstance(proof,dict):return False
    if goal is None:return proof=={'true':True} and proof['true'] is True
    if 'sub' in proof:
        i=proof['sub']
        return type(i) is int and 0<=i<len(cs) and cs[i].issubset(goal)
    assignment={abs(l):l<0 for l in goal}

    def visit(node,values,level):
        if not isinstance(node,dict) or level>3:return False
        ids=node.get('units')
        if not isinstance(ids,(list,tuple)):return False
        for j in ids:
            if type(j) is not int or not 0<=j<len(cs):return False
            row=cs[j]
            if any(values.get(abs(l))==(l>0) for l in row):return False
            free=[l for l in row if abs(l) not in values]
            if len(free)!=1:return False
            values[abs(free[0])]=(free[0]>0)
        if 'conflict' in node:
            j=node['conflict']
            return (type(j) is int and 0<=j<len(cs) and
                    all(abs(l) in values and values[abs(l)]!=(l>0) for l in cs[j]))
        v=node.get('split')
        if type(v) is not int or not 1<=v<=n or v in values or level==3:return False
        a=values.copy();a[v]=False;values[v]=True
        return visit(node.get('zero'),a,level+1) and visit(node.get('one'),values,level+1)
    return visit(proof,assignment,0)


def check_clause(n,source,clause,proof):
    rows=_raw(n,source)
    q,=_raw(n,[clause])
    key=None if any(-l in q for l in q) else tuple(set(q))
    return _verify(tuple(map(frozenset,rows)),key,proof,n)


def check_derived_transport(n,source,target,cert):
    a,b=_raw(n,source),_raw(n,target)
    if not isinstance(cert,dict) or cert.get('kind')!=KIND or not _images(n,cert.get('images')):return False
    proofs=cert.get('clauses')
    if not isinstance(proofs,(tuple,list)) or len(proofs)!=len(b):return False
    a=tuple(map(frozenset,a))
    for target_row, pr in zip(b,proofs):
        # Derive assumptions for making the original target clause false.
        # Deliberately separate from the searcher's literal-pullback routine.
        forced={}; taut=False
        for l in target_row:
            image=cert['images'][abs(l)-1]
            need=l<0   # value the target bit needs to make l false
            if type(image) is bool:
                if image!=need:taut=True;break
            else:
                bit=need if image>0 else not need
                var=abs(image)
                if var in forced and forced[var]!=bit:taut=True;break
                forced[var]=bit
        goal=None if taut else tuple(-v if val else v for v,val in forced.items())
        if not _verify(a,goal,pr,n):return False
    return True


class _OutOfBudget(Exception):pass
_MODEL=object()


class _Prover:
    def __init__(self,n,source,depth,max_queries,max_nodes):
        _validate_depth(depth);_validate_limit(max_queries);_validate_limit(max_nodes)
        self.n=n;self.depth=depth;self.max_queries=max_queries;self.max_nodes=max_nodes
        self.rows=[];self.sets={};self.cache={}
        for ix,c in enumerate(source):
            if any(-l in c for l in c):continue
            c=frozenset(c)
            self.sets.setdefault(c,ix)
            p=sum(1<<(l-1) for l in c if l>0)
            q=sum(1<<(-l-1) for l in c if l<0)
            self.rows.append((ix,p,q,p|q))
        self.stats=dict(queries=0,nodes=0,split_trials=0,unit_steps=0,clause_scans=0,
                        syntactic_hits=0,cache_hits=0,candidate_maps=0,budget_limited=False)

    def _tree(self,ones,zeros,depth):
        s=self.stats
        if self.max_nodes is not None and s['nodes']>=self.max_nodes:raise _OutOfBudget
        s['nodes']+=1
        ids=[]
        while True:
            before=ones|zeros
            active=0
            for ix,p,q,mask in self.rows:
                s['clause_scans']+=1
                if (p&ones)|(q&zeros):continue
                free=mask&~(ones|zeros)
                if not free:return {'units':ids,'conflict':ix}
                if free & (free-1):
                    active |= free
                else:
                    ids.append(ix);s['unit_steps']+=1
                    if p&free:ones|=free
                    else:zeros|=free
            if before==ones|zeros:break
        if not active:return _MODEL
        if not depth:return None
        # Try only variables in an unresolved clause. Search for a small
        # conflict tree; a found full satisfying extension invalidates all tries.
        while active:
            v=active & -active;active-=v
            s['split_trials']+=1
            z=self._tree(ones,zeros|v,depth-1)
            if z is _MODEL:return _MODEL
            if z is None:continue
            o=self._tree(ones|v,zeros,depth-1)
            if o is _MODEL:return _MODEL
            if o is not None:return dict(units=ids,split=v.bit_length(),zero=z,one=o)
        return None

    def prove(self,goal):
        if goal is None:return {'true':True}
        if goal in self.cache:
            self.stats['cache_hits']+=1;return self.cache[goal]
        for j in range(len(goal)+1):
            for t in combinations(goal,j):
                ix=self.sets.get(frozenset(t))
                if ix is not None:
                    self.stats['syntactic_hits']+=1
                    self.cache[goal]={'sub':ix}
                    return self.cache[goal]
        if self.max_queries is not None and self.stats['queries']>=self.max_queries:raise _OutOfBudget
        self.stats['queries']+=1
        ones=sum(1<<(-l-1) for l in goal if l<0);zeros=sum(1<<(l-1) for l in goal if l>0)
        tree=self._tree(ones,zeros,self.depth)
        self.cache[goal]=None if tree is _MODEL else tree
        return self.cache[goal]


def derive_clause(n,source,clause,*,depth=0,max_nodes=None):
    """Return PROVED or UNKNOWN; proofs show A and the negated goal conflict."""
    a=_raw(n,source);q,=_raw(n,[clause]);key=_pull(q,list(range(1,n+1)))
    p=_Prover(n,a,depth,None,max_nodes)
    try:proof=p.prove(key)
    except _OutOfBudget:p.stats['budget_limited']=True;proof=None
    if proof is not None and not check_clause(n,a,q,proof):raise AssertionError('bad clause proof')
    return dict(status='PROVED' if proof is not None else 'UNKNOWN',proof=proof,stats=p.stats)


def derive_transport(n,source,target,*,images=None,depth=0,max_queries=None,max_nodes=None,
                     strategies=('identity','flip')):
    """A fixed-depth polynomial finder, incomplete on unrestricted formulas.

    If images is supplied, only that map is checked. Otherwise shift discovery
    queries all sign patterns on the target supports, then solves tractable
    classes of local admissible-shift tables. Caps charge nonsyntactic queries
    and propagation nodes across the entire call, not each target clause.
    """
    a,b=_raw(n,source),_raw(n,target)
    if images is not None and not _images(n,images):raise ValueError('bad images')
    if isinstance(strategies,(str,bytes)):raise ValueError('bad strategies')
    strategies=tuple(strategies)
    if any(v not in ('identity','flip') for v in strategies):raise ValueError('bad strategy')
    p=_Prover(n,a,depth,max_queries,max_nodes);cert=None
    def attempt(v,method):
        p.stats['candidate_maps']+=1
        proofs=[]
        for row in b:
            found=p.prove(_pull(row,v))
            if found is None:return None
            proofs.append(found)
        c=dict(kind=KIND,images=list(v),method=method,clauses=proofs)
        if not check_derived_transport(n,a,b,c):raise AssertionError('bad derived map proof')
        return c
    try:
        if images is not None:cert=attempt(images,'provided')
        else:
            ident=list(range(1,n+1))
            for strategy in strategies:
                if strategy=='identity':cert=attempt(ident,'identity')
                else:
                    # Keep syntactically raw target rows for final certificate;
                    # dedup for the sign-pattern search itself. All tables are
                    # on the ORIGINAL named coordinates.
                    target_rows=tuple(sorted({_pull(c,ident) for c in b}-{None}))
                    supports={tuple(map(abs,c)) for c in target_rows}
                    virt=[]
                    for vs in sorted(supports):
                        for signs in product((1,-1),repeat=len(vs)):
                            clause=tuple(x*y for x,y in zip(vs,signs))
                            if p.prove(clause) is not None:virt.append(clause)
                    candidate=_flips(n,tuple(virt),target_rows)
                    if candidate is not None:
                        cert=attempt(candidate['images'],'derived-'+candidate['method'])
                if cert is not None:break
    except _OutOfBudget:p.stats['budget_limited']=True
    return dict(status='FOUND' if cert is not None else 'UNKNOWN',certificate=cert,stats=p.stats)
