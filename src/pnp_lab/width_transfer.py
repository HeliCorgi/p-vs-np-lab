"""Resolution retractions, a genuinely SAT consequence, and asymmetric siblings.

Clauses are sets of signed 1-based integers. Traces are sequences of
("a", input index), ("r", positive-line index, negative-line index, pivot)
or ("w", line index, superclause). No extension variables or learning oracle.
"""
from itertools import combinations, product

from .simple_support import GADGET, simple_support_image


def _cl(c):
    c=frozenset(c)
    if any(type(v) is not int or not v for v in c):
        raise ValueError('invalid literal')
    return c


def _ix(i,n):
    if type(i) is not int or not 0<=i<n:raise ValueError('bad proof index')
    return i


def replay(axioms,proof):
    axioms=list(map(_cl,axioms));rows=[]
    for op,*args in proof:
        if op=='a' and len(args)==1:
            c=axioms[_ix(args[0],len(axioms))]
        elif op=='r' and len(args)==3:
            i,j,p=args
            a,b=rows[_ix(i,len(rows))],rows[_ix(j,len(rows))]
            if type(p) is not int or p<=0 or p not in a or -p not in b:raise ValueError('bad pivot')
            c=(a-{p})|(b-{-p})
        elif op=='w' and len(args)==2:
            i,c=args;c=_cl(c)
            if not rows[_ix(i,len(rows))]<=c:raise ValueError('not weakening')
        else:raise ValueError('bad proof operation')
        rows.append(c)
    return rows


def pull(clause,images):
    """None denotes true, including complementary coordinates after identification."""
    out=set()
    for l in clause:
        v=images[abs(l)-1]
        if type(v) is bool:
            if v==(l>0):return None
        else:
            if type(v) is not int or not v:raise ValueError('invalid image')
            z=v if l>0 else -v
            if -z in out:return None
            out.add(z)
    return frozenset(out)


def retract_proof(source,target,images,proof):
    """Translate a resolution trace ending in a nontrue clause (in particular empty).

    Each target axiom must map to true or contain a source axiom. Each live
    proof line is represented by a derivation of a SUBclause of its image.
    Produces ordinary resolution, no weakening steps needed. The final
    return drops trailing lines unused by the translated conclusion.
    """
    s=list(map(_cl,source)); t=list(map(_cl,target)); old=replay(t,proof)
    if not old or pull(old[-1],images) is None:raise ValueError('nontrue conclusion required')
    # A subclause contains only literals occurring in the (usually small) image.
    src={c:i for i,c in enumerate(s)}
    out=[]; rows=[]; refs=[]
    def emit(step,row):
        out.append(step);rows.append(row);return len(out)-1
    for step,original in zip(proof,old):
        c=pull(original,images)
        if c is None: refs.append(None);continue
        if step[0]=='a':
            hit=next((frozenset(a) for r in range(len(c)+1) for a in combinations(sorted(c),r)
                      if frozenset(a) in src),None)
            if hit is None:raise ValueError('unjustified projected input clause')
            at=emit(('a',src[hit]),hit)
        elif step[0]=='w':
            at=refs[step[1]]
            if at is None:raise AssertionError('nontrue weakening of true')
        else:
            _,i,j,p=step
            x,y=refs[i],refs[j]
            if x is not None and rows[x]<=c:at=x
            elif y is not None and rows[y]<=c:at=y
            else:
                m=images[p-1]
                if type(m) is bool or x is None or y is None:raise AssertionError('projection invariant')
                if m<0:x,y=y,x;m=-m
                if m not in rows[x] or -m not in rows[y]:raise AssertionError('missing projected pivot')
                at=emit(('r',x,y,m),(rows[x]-{m})|(rows[y]-{-m}))
        if not rows[at]<=c:raise AssertionError('image not strengthened')
        refs.append(at)
    return out[:refs[-1]+1]


def restrict(cs,v,b):
    return tuple(tuple(l for l in c if abs(l)!=v) for c in cs
                 if (v if b else -v) not in c)


def guarded(n,H,*,contradict_on_true):
    """Exact phase-12 encoding of a switched formula. No special solvers used."""
    s=n+1;p=n+2; m=p; f=[]; down=list(range(1,n+1))+[False,False]
    for raw in H:
        c=tuple(dict.fromkeys(raw))
        if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):
            raise ValueError('expected width-three formula')
        if any(-l in c for l in c):continue
        if len(c)<=2:f.append((s,)+c)
        else:
            a,b,z=c;m+=1
            f.extend(((s,a,m),(-m,b,z)))
            down.append(-a)
    # Need a concrete occurrence port for the branch; all benchmarks have one.
    if not f:raise ValueError('need at least one nontautological source clause')
    if contradict_on_true:f.extend(((-s,p),(-s,-p)))
    N,F,wires=simple_support_image(m,f)
    images=[False]*N
    # All gadget bits true also satisfy the gadget minus its first clause.
    for i in range(6):images[i]=True
    images[-2]=True
    for j,vs in enumerate(wires):
        for v in vs: images[v-1]=down[j]
    # A visible satisfying model on the consequence-only version, g=true,
    # all input bits and all split auxiliaries false. Both padding witnesses true.
    model=63 | (3<<(N-2)) | sum(1<<(v-1) for v in wires[s-1])
    return dict(n=N,cnf=F,gate=wires[s-1][0],images=tuple(images),
                model=None if contradict_on_true else model)


def _pins_trace(cs):
    cnf=list(map(_cl,cs)); proof=[]; rows=[]
    def emit(step,row):
        proof.append(step);rows.append(row);return len(rows)-1
    axi={c:emit(('a',i),c) for i,c in enumerate(cnf)}
    seed=[_cl(c) for c in GADGET[1:]]
    if any(c not in axi for c in seed):raise ValueError('forcing gadget absent')
    def tree(values):
        for c in seed:
            if all(abs(l) in values and values[abs(l)]!=(l>0) for l in c):return axi[c]
        p=next(k for k in range(1,7) if k not in values)
        a=tree(dict(values)|{p:False})
        if p not in rows[a]:return a
        b=tree(dict(values)|{p:True})
        if -p not in rows[b]:return b
        return emit(('r',a,b,p),(rows[a]-{p})|(rows[b]-{-p}))
    for i in (4,5,6):
        at=tree({i:False})
        if rows[at]!=frozenset({i}):raise AssertionError('invalid forcing proof')
    return proof,rows


def easy_refutation(cs):
    """Find an ordinary resolution refutation after the six-bit forcing proof.

    Unit propagation suffices on the easy sibling. Distinct pivots are
    propagated once; at most three resolution steps per activated input row.
    """
    proof,rows=_pins_trace(cs)
    initial=list(map(_cl,cs))
    ax={c:i for i,c in enumerate(rows[:len(initial)])}
    units={next(iter(c)):i for i,c in enumerate(rows) if len(c)==1}
    while True:
        for l,i in units.items():
            if l>0 and -l in units:
                return proof+[('r',i,units[-l],l)]
        before=len(units)
        for c in initial:
            if any(l in units for l in c):continue
            unknown={l for l in c if -l not in units}
            if len(unknown)>1:continue
            at=ax[c];current=c
            for lit in sorted(c-unknown):
                ui=units[-lit]
                i,j=(at,ui) if lit>0 else (ui,at)
                proof.append(('r',i,j,abs(lit)));current=current-{lit};rows.append(current);at=len(rows)-1
            if not unknown:
                # If an input empty clause was used, truncate to that axiom.
                return proof[:at+1]
            units[next(iter(unknown))]=at
        if len(units)==before:raise ValueError('propagation did not refute input')


def cubic_tseitin(vertices,edges,odd=True):
    edges=list(edges);incident=[[] for _ in range(vertices)];cs=[]
    if any(not 0<=a<b<vertices for a,b in edges) or len(set(edges))!=len(edges):raise ValueError('bad graph')
    for i,(a,b) in enumerate(edges,1):incident[a].append(i);incident[b].append(i)
    for v,vs in enumerate(incident):
        if len(vs)!=3:raise ValueError('degree must equal three')
        for bits in product((0,1),repeat=3):
            if sum(bits)%2!=int(v==0 and odd):
                cs.append(tuple(-q if s else q for q,s in zip(vs,bits)))
    return len(edges),tuple(cs)


def closure_small(cs,w):
    """Complete width-w saturation for tiny controls only, no weakening needed."""
    from collections import defaultdict
    rows=[];proof=[];index={};by=defaultdict(list)
    def add(c,op):
        if len(c)>w or any(-l in c for l in c) or c in index:return
        i=len(rows);index[c]=i;rows.append(c);proof.append(op)
        for l in c:by[l].append(i)
    for i,c in enumerate(cs):add(_cl(c),('a',i))
    i=0
    while i<len(rows) and frozenset() not in index:
        a=rows[i]
        for l in sorted(a):
            for j in by[-l]:
                if j>=i:break
                b=rows[j];r=(a-{l})|(b-{-l})
                left,right=(i,j) if l>0 else (j,i)
                add(r,('r',left,right,abs(l)))
        i+=1
    got=index.get(frozenset())
    return dict(contradiction=got is not None,known=len(rows),
                proof=(None if got is None else proof[:got+1]))
