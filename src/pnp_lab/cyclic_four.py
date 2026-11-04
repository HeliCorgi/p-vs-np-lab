"""Recognize hidden cyclic order-four conservation over Boolean 3-CNFs.

This is ring arithmetic, not Gaussian elimination in a nonexistent prime
field modulo 4. UNSAT proofs sum locally checked Boolean modular rows.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations,permutations,product

from .modular_hull import _input


def _key(c):
    return tuple(sorted(set(c),key=abs))


def _index(cs):
    signed={};occ=defaultdict(list)
    for i,c in enumerate(cs):
        d=_key(c)
        if any(-l in d for l in d) or d in signed:continue
        signed[d]=i
        for l in d:occ[l].append(d)
    return signed,occ


def _domains(signed,occ):
    blocks=[];owners={}
    for h in sorted(l for l in occ if l>0):
        if len(occ[h])!=1 or len(occ[-h])!=1:continue
        (a,),(b,)=occ[h],occ[-h]
        if len(a)!=3 or len(b)!=3:continue
        A=tuple(v for v in a if v!=h);B=tuple(v for v in b if v!=-h)
        lits=_key((*A,*B))
        if len(set(map(abs,lits)))!=4:continue
        pairs=[_key((-x,-y)) for x,y in combinations(lits,2)]
        if not all(c in signed for c in pairs):continue
        scopes=(*map(abs,lits),h)
        if any(v in owners for v in scopes):return None,None
        j=len(blocks)
        for v in scopes:owners[v]=j
        blocks.append((lits,h,B,{signed[c] for c in [a,b,*pairs]}))
    return blocks,owners


def _terms(group,rows,blocks,owners):
    idx={b:t for t,b in enumerate(group)}
    test=[]
    for c,_ in rows:
        row=[]
        for l in c:
            j=owners[abs(l)];I,h,B,_=blocks[j]
            if abs(l)==h:cond=tuple((k in B)==(l>0) for k in I)
            else:cond=tuple((u==l if l in I else u!=-l) for u in I)
            row.append((idx[j],cond))
        test.append(row)
    return [w for w in product(range(4),repeat=len(group)) if all(any(vals[w[j]] for j,vals in c) for c in test)]


PERMS=tuple((0,*p) for p in permutations((1,2,3)))


@lru_cache(maxsize=256)
def _candidates(arity,table):
    if len(table)!=4**(arity-1):return ()
    first,*rest=table
    choices=[]
    for pi in product(PERMS,repeat=arity):
        b=sum(p[x] for p,x in zip(pi,first))%4
        if all(sum(p[x] for p,x in zip(pi,w))%4==b for w in rest):
            choices.append((pi,b))
    return tuple(choices)


def _opposite(p):
    return tuple(-v%4 for v in p)


def _minus(d,a,e):
    for j,z in e.items():
        u=(d.get(j,0)-a*z)%4
        if u:d[j]=u
        else:d.pop(j,None)


def _mul(d,a):
    return {j:(a*v)%4 for j,v in d.items() if (a*v)%4}


def _solve(rows,n):
    todo=[(d.copy(),b,{i:1}) for i,(d,b) in enumerate(rows)]
    first=[]
    while True:
        pivot=next(((i,j) for i,(d,_,_) in enumerate(todo) for j,c in d.items() if c%2),None)
        if pivot is None:break
        i,j=pivot;d,b,t=todo.pop(i)
        a=d[j];d,t=_mul(d,a),_mul(t,a);b=b*a%4 # 1 and 3 are self-inverse
        first.append((j,d,b))
        for k,(r,s,u) in enumerate(todo):
            scale=r.get(j,0)
            if scale:
                _minus(r,scale,d);_minus(u,scale,t);todo[k]=(r,(s-scale*b)%4,u)
    even={}
    for r,b,u in todo:
        if b%2:return None,_mul(u,2),len(first),len(even)
        while r:
            j=min(r)
            if j not in even:
                even[j]=(r,b,u);break
            d,h,t=even[j];_minus(r,1,d);_minus(u,1,t);b=(b-h)%4
        else:
            if b:return None,u,len(first),len(even)
    point=[0]*n
    for j,(d,b,_) in sorted(even.items(),reverse=True):
        point[j]=((b-sum(z*point[k] for k,z in d.items() if k!=j))%4)//2
    for j,d,b in reversed(first):
        point[j]=(b-sum(z*point[k] for k,z in d.items() if k!=j))%4
    return point,None,len(first),len(even)


@lru_cache(maxsize=16)
def _columns(w):
    # Bit i of a column is the coordinate on Boolean assignment number i.
    ones=(1<<(1<<w))-1
    return tuple(((((1<<(1<<j))-1)<<(1<<j))*(ones//((1<<(2<<j))-1))) for j in range(w))


def check_cyclic_four(n,clauses,result):
    """Replay raw SAT point or modular rows; no block finder/permutations used."""
    try:
        cs=_input(n,clauses)
        if result['status']=='SAT':
            x=result['witness']
            return (result['certificate'] is None and type(x) is int and 0<=x and x.bit_length()<=n
                    and all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs))
        if result['status']!='UNSAT' or result['witness'] is not None:return False
        cert=result['certificate']
        if cert['kind']!='boolean-cyclic-four-v1' or not isinstance(cert['terms'],list) or not cert['terms']:return False
        combined={};total=0
        for row in cert['terms']:
            vs=row['scope'];cf=row['coeff'];b=row['rhs'];ids=row['clauses']
            if (not isinstance(vs,list) or len(vs)>15 or len(set(vs))!=len(vs)
                or any(type(v) is not int or not 1<=v<=n for v in vs)
                or not isinstance(cf,list) or len(cf)!=len(vs) or any(type(a) is not int or not 0<=a<4 for a in cf)
                or type(b) is not int or not 0<=b<4 or not isinstance(ids,list) or not ids
                or any(type(i) is not int or not 0<=i<len(cs) for i in ids)):return False
            ix={v:i for i,v in enumerate(vs)};cols=_columns(len(vs));full=(1<<(1<<len(vs)))-1
            valid=full
            for i in ids:
                sat=0
                for l in cs[i]:
                    z=cols[ix[abs(l)]];sat |= z if l>0 else full^z
                valid &= sat
            lo=hi=0
            for j,a in enumerate(cf):
                col=cols[j]
                if a%2:hi ^= lo&col;lo ^= col
                if a//2:hi ^= col
                combined[vs[j]]=(combined.get(vs[j],0)+a)%4
            ok=(lo if b%2 else full^lo)&(hi if b//2 else full^hi)
            if valid & (full^ok):return False
            total=(total+b)%4
        return not any(combined.values()) and total!=0
    except (TypeError,KeyError,AttributeError,IndexError,ValueError):return False


def solve_cyclic_four(n,clauses):
    cs=_input(n,clauses);signed,occ=_index(cs)
    stats=dict(blocks=0,local_groups=0,local_words=0,equations=0,unit_pivots=0,even_pivots=0)
    def answer(status,reason,witness=None,cert=None):
        out=dict(status=status,reason=reason,stats=stats,witness=witness,certificate=cert)
        if status!='UNKNOWN' and not check_cyclic_four(n,cs,out):raise AssertionError('invalid Z4 answer')
        return out
    if () in signed:
        term=dict(scope=[],coeff=[],rhs=1,clauses=[signed[()]])
        return answer('UNSAT','empty clause',cert=dict(kind='boolean-cyclic-four-v1',terms=[term]))
    blocks,owners=_domains(signed,occ)
    if blocks is None:return answer('UNKNOWN','overlapping private four-state domains')
    stats['blocks']=len(blocks)
    if set(map(abs,occ))!=set(owners):return answer('UNKNOWN','uncovered active variable')
    groups=defaultdict(list)
    for c,i in sorted(signed.items()):
        if not c:continue
        groups[tuple(sorted({owners[abs(l)] for l in c}))].append((c,i))
    coordinates={};equations=[];leaves=[]
    stats['local_groups']=len(groups)
    def local(group,rows,coeff,rhs):
        ids=set(i for _,i in rows);sc=set()
        for j in group:
            I,h,_,ii=blocks[j];sc.update(map(abs,I));sc.add(h);ids.update(ii)
        vs=sorted(sc)
        return dict(scope=vs,clauses=sorted(ids),coeff=[coeff.get(v,0) for v in vs],rhs=rhs)
    for g,rows in sorted(groups.items()):
        table=_terms(g,rows,blocks,owners);stats['local_words']+=4**len(g)
        if len(table)==4**len(g):continue
        if not table:
            return answer('UNSAT','empty four-state table',cert=dict(kind='boolean-cyclic-four-v1',terms=[local(g,rows,{},1)]))
        if len(g)!=3:return answer('UNKNOWN','nontrivial group is not ternary')
        candidates=_candidates(len(g),tuple(table))
        if not candidates:return answer('UNKNOWN','local table is not a cyclic addition relation')
        pi,b=candidates[0];r={};boolrow={};rhs=b
        for j,p in zip(g,pi):
            canon=min(p,_opposite(p))
            if coordinates.setdefault(j,canon)!=canon:return answer('UNKNOWN','incompatible local state calibrations')
            sign=1 if p==canon else 3;r[j]=sign
            for l,w in zip(blocks[j][0],p):
                if l>0:boolrow[l]=w
                else:boolrow[-l]=-w%4;rhs=(rhs-w)%4
        equations.append((r,b));leaves.append(local(g,rows,boolrow,rhs));stats['equations']+=1
    point,proof,stats['unit_pivots'],stats['even_pivots']=_solve(equations,len(blocks))
    if proof is not None:
        terms=[]
        for i,k in sorted(proof.items()):
            leaf=leaves[i]
            terms.append(dict(leaf,coeff=[(k*c)%4 for c in leaf['coeff']],rhs=k*leaf['rhs']%4))
        stats['residual_rhs']=sum(t['rhs'] for t in terms)%4
        return answer('UNSAT','modular equation contradiction',cert=dict(kind='boolean-cyclic-four-v1',terms=terms))
    x=0
    for j,(I,h,B,_) in enumerate(blocks):
        chosen=I[coordinates.get(j,(0,1,2,3)).index(point[j])]
        for l in I:
            if (l==chosen)==(l>0):x|=1<<(abs(l)-1)
        if chosen in B:x|=1<<(h-1)
    return answer('SAT','verified Boolean assignment from cyclic-four system',witness=x)
