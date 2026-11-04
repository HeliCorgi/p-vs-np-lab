"""Integral affine character profile of a small Boolean relation.

For local model words x, quotient Z^(d+1) by the Z-row span of (x,1).
Candidate-scope discovery uses Boolean domain incidence only. Neither the
table reducer nor its independent verifier receives a group, law or modulus.
"""
from collections import Counter
from .modular_hull import _input
from .cyclic_four import _columns, _domains, _index

MAX_D=15
MAX_MODELS=256
MAX_OPS=20000
MAX_BITS=512


def _vs(n,scope):
    vs=tuple(scope)
    if len(vs)>MAX_D or len(set(vs))!=len(vs) or any(type(v) is not int or not 1<=v<=n for v in vs):
        raise ValueError("invalid named local scope")
    return vs


def _table(cs,vs):
    """Truth-table bit parallel input evaluator, d <= 15."""
    d=len(vs);pos={v:i for i,v in enumerate(vs)};cols=_columns(d)
    full=(1<<(1<<d))-1;bits=full
    for c in cs:
        if not all(abs(l) in pos for l in c):continue
        ok=0
        for l in c:
            col=cols[pos[abs(l)]];ok |= col if l>0 else full^col
        bits &= ok
    return bits


def _raw_words(cs,vs):
    """Separate checker evaluator: branch on the next raw bit and prune dead clauses."""
    pos={v:i for i,v in enumerate(vs)};end=[[] for v in vs]
    for c in cs:
        if not all(abs(l) in pos for l in c):continue
        if not c:return []
        end[max(pos[abs(l)] for l in c)].append(tuple((pos[abs(l)],l>0) for l in c))
    frontier=[0]
    for i,group in enumerate(end):
        new=[]
        for x in frontier:
            for y in (x,x|(1<<i)):
                if all(any(bool(y>>j&1)==t for j,t in c) for c in group):new.append(y)
        frontier=new
    return sorted(frontier)


def _matrix(d,ws):
    return [[(w>>j)&1 for j in range(d)]+[1] for w in ws]


def _limits(max_models,max_ops,max_bits):
    for x,cap in ((max_models,MAX_MODELS),(max_ops,MAX_OPS),(max_bits,MAX_BITS)):
        if type(x) is not int or not 0<=x<=cap:raise ValueError("invalid safety cap")


def torsion_table(d,words,*,max_models=MAX_MODELS,max_ops=MAX_OPS,max_bits=MAX_BITS):
    """words is a bitset; bit w is one precisely when w is a local Boolean model."""
    if type(d) is not int or not 0<=d<=MAX_D or type(words) is not int or words<0 or words.bit_length()>1<<d:
        raise ValueError("invalid Boolean table")
    _limits(max_models,max_ops,max_bits);models=words.bit_count();ops=[];ds=[]
    def unknown(why):
        return dict(status='UNKNOWN',reason=why,models=models,operations=len(ops),certificate=None)
    if models>max_models:return unknown('model-word cap')
    if max_bits==0 and models:return unknown('integer bit cap')
    ws=[]
    while words:
        b=words&-words;ws.append(b.bit_length()-1);words-=b
    A=_matrix(d,ws);m=len(A);n=d+1
    class _Cap(Exception):pass
    def op(tag,i,j=None,t=None):
        if len(ops)>=max_ops:raise _Cap('operation cap')
        if tag=='R':A[i],A[j]=A[j],A[i]
        elif tag=='C':
            for r in A:r[i],r[j]=r[j],r[i]
        elif tag=='N':A[i]=[-v for v in A[i]]
        elif tag=='r':
            A[i]=[u+t*v for u,v in zip(A[i],A[j])]
            if any(v.bit_length()>max_bits for v in A[i]):raise _Cap('integer bit cap')
        elif tag=='c':
            for r in A:
                r[i]+=t*r[j]
                if r[i].bit_length()>max_bits:raise _Cap('integer bit cap')
        ops.append([tag,i]+([] if j is None else [j])+([] if t is None else [t]))
    try:
        for k in range(min(m,n)):
            entry=min(((abs(A[i][j]),i,j) for i in range(k,m) for j in range(k,n) if A[i][j]),default=None)
            if entry is None:break
            _,ri,ci=entry
            if ri!=k:op('R',k,ri)
            if ci!=k:op('C',k,ci)
            while True:
                moved=False
                for i in range(k+1,m):
                    if not A[i][k]:continue
                    q,r=divmod(A[i][k],A[k][k])
                    if q:op('r',i,k,-q)
                    if r:
                        op('R',i,k);moved=True;break
                if moved:continue
                for j in range(k+1,n):
                    if not A[k][j]:continue
                    q,r=divmod(A[k][j],A[k][k])
                    if q:op('c',j,k,-q)
                    if r:
                        op('C',j,k);moved=True;break
                if moved:continue
                bad=next((i for i in range(k+1,m) if any(A[i][j]%A[k][k] for j in range(k+1,n))),None)
                if bad is None:break
                # Bring a nonmultiple into the pivot row: one Euclidean column
                # pass then reduces the absolute pivot, ensuring termination.
                op('r',k,bad,1)
            if A[k][k]<0:op('N',k)
            ds.append(A[k][k])
    except _Cap as cap:return unknown(str(cap))
    cert=dict(kind='boolean-local-smith-v1',width=d,models=models,diagonal=ds,ops=ops)
    return dict(status='PROFILE',reason='empty local relation' if not models else 'checked integer table',
                models=models,operations=len(ops),rank=len(ds),free_rank=n-len(ds),
                torsion=[v for v in ds if v>1],certificate=cert)


def check_local_torsion(n,clauses,scope,cert):
    """Independently enumerate the original local models and replay invertible steps."""
    try:
        cs=_input(n,clauses);vs=_vs(n,scope);d=len(vs)
        if not isinstance(cert,dict) or cert.get('kind')!='boolean-local-smith-v1' or type(cert['width']) is not int or cert['width']!=d:return False
        ws=_raw_words(cs,vs)
        if type(cert['models']) is not int or cert['models']!=len(ws) or len(ws)>MAX_MODELS:return False
        a=_matrix(d,ws);rows=len(a);cols=d+1
        ds=cert['diagonal'];ops=cert['ops']
        if not isinstance(ds,list) or len(ds)>min(rows,cols) or any(type(x) is not int or x<=0 for x in ds) or any(y%x for x,y in zip(ds,ds[1:])):return False
        if not isinstance(ops,list) or len(ops)>MAX_OPS:return False
        for step in ops:
            if not isinstance(step,(list,tuple)) or len(step)<2:return False
            t,i,*rest=step
            if t not in ('R','C','r','c','N'):return False
            bound=rows if t in ('R','r','N') else cols
            if type(i) is not int or not 0<=i<bound:return False
            if t=='N':
                if rest:return False
                a[i]=list(map(int.__neg__,a[i]));continue
            if len(rest)!=(2 if t in ('r','c') else 1):return False
            j=rest[0]
            if type(j) is not int or j==i or not 0<=j<bound:return False
            if t=='R':a[i],a[j]=a[j],a[i]
            elif t=='C':
                for row in a:row[i],row[j]=row[j],row[i]
            else:
                scale=rest[1]
                if type(scale) is not int or scale.bit_length()>MAX_BITS+1:return False
                if t=='r':
                    for h in range(cols):a[i][h]+=scale*a[j][h]
                    if any(x.bit_length()>MAX_BITS for x in a[i]):return False
                else:
                    for row in a:
                        row[i]+=scale*row[j]
                        if row[i].bit_length()>MAX_BITS:return False
        return all(x==(ds[i] if i==j and i<len(ds) else 0)
                   for i,row in enumerate(a) for j,x in enumerate(row))
    except (ValueError,KeyError,TypeError,IndexError):return False


def scan_local_torsion(n,clauses,*,max_scopes=None,max_models=MAX_MODELS,max_ops=MAX_OPS,max_bits=MAX_BITS):
    if max_scopes is not None and (type(max_scopes) is not int or max_scopes<0):raise ValueError("invalid scope cap")
    _limits(max_models,max_ops,max_bits)
    cs=_input(n,clauses);s,occ=_index(cs);bs,owner=_domains(s,occ)
    def report(why,available,scanned,unknown,counts,examples):
        return dict(reason=why,available_scopes=available,scanned_scopes=scanned,unknown_scopes=unknown,
                    complete_for_scopes=why=='scanned' and unknown==0 and available==scanned,
                    histogram={str(list(k)):v for k,v in sorted(counts.items())},examples=examples)
    if bs is None:return report('overlapping candidate blocks',0,0,0,{},[])
    groups=set()
    for c in s:
        if not c or any(abs(l) not in owner for l in c):continue
        g=tuple(sorted({owner[abs(l)] for l in c}))
        if len(g)==3:groups.add(g)
    scopes=[tuple(sorted(v for j in g for v in (*map(abs,bs[j][0]),bs[j][1]))) for g in sorted(groups)]
    chosen=scopes if max_scopes is None else scopes[:max_scopes]
    counts=Counter();examples=[];unknown=0
    for vs in chosen:
        q=torsion_table(len(vs),_table(cs,vs),max_models=max_models,max_ops=max_ops,max_bits=max_bits)
        if q['status']=='UNKNOWN':unknown+=1;continue
        t=tuple(q['torsion']);counts[t]+=1
        if counts[t]==1:
            if not check_local_torsion(n,cs,vs,q['certificate']):raise AssertionError('nonreplaying Smith certificate')
            examples.append(dict(scope=list(vs),torsion=list(t),free_rank=q['free_rank'],certificate=q['certificate']))
    return report('scanned',len(scopes),len(chosen),unknown,counts,examples)


def local_torsion(n,clauses,scope,**limits):
    cs=_input(n,clauses);vs=_vs(n,scope)
    return torsion_table(len(vs),_table(cs,vs),**limits)


def torsion_characters(cert):
    """Extract the chosen affine characters; caller first verifies the Smith trace."""
    n=cert['width']+1;v=[[int(i==j) for j in range(n)] for i in range(n)]
    for step in cert['ops']:
        op=step[0]
        if op=='C':
            i,j=step[1:]
            for row in v:row[i],row[j]=row[j],row[i]
        elif op=='c':
            i,j,a=step[1:]
            for row in v:row[i]+=a*row[j]
    return [dict(modulus=t,coeff=[row[j]%t for row in v[:-1]],rhs=(-v[-1][j])%t)
            for j,t in enumerate(cert['diagonal']) if t>1]
