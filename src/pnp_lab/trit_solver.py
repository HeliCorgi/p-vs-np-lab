"""Decide signed one-hot Boolean encodings of local affine ternary relations."""
from collections import defaultdict
from itertools import combinations,product

from .modular_hull import _input,modular_hull_refute,check_modular_hull


def _normalize(cs):
    out=set()
    for c in cs:
        s=frozenset(c)
        if not any(-l in s for l in s):out.add(tuple(sorted(s,key=abs)))
    return out


def _blocks(cs):
    blocks=[]
    for c in sorted(cs):
        if len(c)==3 and all(tuple(-l for l in pair) in cs for pair in combinations(c,2)):
            blocks.append(c)
    # Multiple candidates on the same three variables or overlapping triples
    # are declined. Never choose an arbitrary disjoint subset.
    tab={}
    for i,c in enumerate(blocks):
        for val,lit in enumerate(c):
            v=abs(lit)
            if v in tab:return None,None
            tab[v]=(i,val,lit>0)
    return blocks,tab


def _independent(row,basis):
    r={k:v%3 for k,v in row.items() if v%3}
    while r:
        j=min(r);k=r[j]
        if j not in basis:
            inv=pow(k,-1,3)
            basis[j]={v:(a*inv)%3 for v,a in r.items()}
            return True
        for h,b in basis[j].items():
            c=(r.get(h,0)-k*b)%3
            if c:r[h]=c
            else:r.pop(h,None)
    return False


def _local(group,rows):
    where={v:i for i,v in enumerate(group)}
    table=[]
    for word in product(range(3),repeat=len(group)):
        if all(any((word[where[j]]==val)==same for j,val,same in row) for row in rows):table.append(word)
    if not table:return 'empty',[]
    out=[];piv={}
    for normal in product(range(3),repeat=len(group)):
        if next((u for u in normal if u),0)!=1:continue
        rhs=sum(x*y for x,y in zip(normal,table[0]))%3
        if all(sum(x*y for x,y in zip(normal,z))%3==rhs for z in table[1:]):
            if _independent({j:v for j,v in enumerate(normal)},piv):
                out.append(({v:k for v,k in zip(group,normal) if k},rhs))
    return ('affine' if len(table)==3**(len(group)-len(out)) else 'nonaffine'),out


def _point(rows,size):
    """Construct an F3 point; None only on inconsistent equations."""
    piv={}
    for r0,b in rows:
        r=r0.copy()
        while r:
            j=min(r);scale=r[j]
            if j not in piv:
                u=pow(scale,-1,3)
                piv[j]=({v:(a*u)%3 for v,a in r.items()},b*u%3)
                break
            older,rhs=piv[j];b=(b-scale*rhs)%3
            for v,t in older.items():
                z=(r.get(v,0)-scale*t)%3
                if z:r[v]=z
                else:r.pop(v,None)
        else:
            if b:return None,len(piv)
    val=[0]*size
    for j in sorted(piv,reverse=True):
        r,b=piv[j];val[j]=(b-sum(c*val[v] for v,c in r.items() if v!=j))%3
    return val,len(piv)


def check_trit_answer(n,clauses,result):
    """Verify a decided result only. An unknown status supplies no evidence."""
    try:
        cs=_input(n,clauses)
        if not isinstance(result,dict):return False
        if result['status']=='UNSAT':
            return result['witness'] is None and result['certificate']['prime']==3 and check_modular_hull(n,cs,result['certificate'])
        if result['status']!='SAT':return False
        x=result['witness']
        return (type(x) is int and 0<=x and x.bit_length()<=n and result['certificate'] is None
                and all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs))
    except (AttributeError,ValueError,TypeError,KeyError,IndexError):
        return False


def solve_trit_affine(n,clauses):
    cs=_input(n,clauses);formula=_normalize(cs);active={abs(l) for c in formula for l in c}
    stats=dict(blocks=0,groups=0,groups_checked=0,local_trit_words=0,affine_rows=0,rank=0)
    def answer(status,reason,witness=None,certificate=None):
        res=dict(status=status,reason=reason,witness=witness,certificate=certificate,stats=stats)
        if status!='UNKNOWN' and not check_trit_answer(n,cs,res):raise AssertionError('invalid trit answer')
        return res
    def refute(reason):
        m=modular_hull_refute(n,cs,prime=3)
        if m['status']!='UNSAT':raise AssertionError('lost affine contradiction in one-hot translation')
        stats['proof_terms']=len(m['certificate']['terms'])
        return answer('UNSAT',reason,certificate=m['certificate'])
    if () in formula:return refute('empty clause')
    blocks,tab=_blocks(formula)
    if blocks is None:return answer('UNKNOWN','overlapping detected one-hot triples')
    stats['blocks']=len(blocks)
    if set(tab)!=active:return answer('UNKNOWN','active variables not covered by one-hot triples')
    groups=defaultdict(list)
    for row in sorted(formula):
        transformed=[]
        for l in row:
            j,val,sign=tab[abs(l)]
            transformed.append((j,val,sign==(l>0)))
        group=tuple(sorted({j for j,_,_ in transformed}))
        groups[group].append(transformed)
    stats['groups']=len(groups)
    equations=[]
    for group,rows in sorted(groups.items(),key=lambda g:(len(g[0]),g[0])):
        stats['groups_checked']+=1;stats['local_trit_words']+=3**len(group)
        typ,eq=_local(group,rows)
        if typ=='empty':return refute('empty local trit relation')
        if typ=='nonaffine':return answer('UNKNOWN','nonaffine local trit relation')
        equations.extend(eq);stats['affine_rows']+=len(eq)
    point,stats['rank']=_point(equations,len(blocks))
    if point is None:return refute('inconsistent ternary equations')
    x=sum(1<<(v-1) for v,(j,b,sign) in tab.items() if (point[j]==b)==sign)
    return answer('SAT','verified Boolean assignment from affine ternary solution',witness=x)
