"""Prove contradictions by combining affine equations common to two bit cases.

Each equation is an augmented integer (variable mask << 1 | right side).
All returned UNSAT proofs are replayed by direct truth tables on original
clause IDs, Boolean case analysis, and integer XOR. One polynomial pass,
not a complete SAT method. No guesses, branch products, or truth tables on n.
"""
from collections import defaultdict


def _raw(n, clauses):
    if type(n) is not int or n < 0:
        raise ValueError('expected nonnegative scope')
    out=[]
    for c in clauses:
        c=tuple(c)
        if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):
            raise ValueError('expected signed 3-CNF')
        out.append(c)
    return tuple(out)


def _leaves(indexed):
    groups=defaultdict(dict)
    for ix,c in indexed:
        c=frozenset(c)
        if any(-l in c for l in c): continue
        if not c:
            return [(1,[ix])]
        mask=sum(1<<(abs(l)-1) for l in c)
        neg=sum(1<<(abs(l)-1) for l in c if l<0)
        groups[mask][neg]=ix
    rows=[]
    for mask,patterns in groups.items():
        for parity in (0,1):
            ids=[i for p,i in patterns.items() if p.bit_count()%2==parity]
            if len(ids)==1<<(mask.bit_count()-1):
                rows.append(((mask<<1)|(parity^1),ids))
    return rows


def _reduce(row,why,basis):
    while row:
        j=row.bit_length()-1
        if j not in basis: break
        a,b=basis[j]
        row,why=row^a,why^b
    return row,why


def _selected(seq,idx):
    while idx:
        bit=idx & -idx
        yield seq[bit.bit_length()-1]
        idx-=bit


def _common(left,right):
    basis={}
    for i,(a,_) in enumerate(left):
        rem,proof=_reduce(a,1<<i,basis)
        if rem: basis[rem.bit_length()-1]=rem,proof
    shift=len(left)
    for j,(b,_) in enumerate(right):
        rem,proof=_reduce(b,1<<(shift+j),basis)
        if rem:
            basis[rem.bit_length()-1]=rem,proof
        else:
            ls=list(_selected(left,proof & ((1<<shift)-1)))
            if not ls: continue
            a=0
            for row,_ in ls: a^=row
            if a: yield a,ls,list(_selected(right,proof>>shift))


def check_split_parity(n, clauses, certificate):
    """Independent checker. No grouping, basis computation or search is replayed."""
    try:
        cs=_raw(n,clauses)
        if not isinstance(certificate,dict) or certificate.get('kind')!='split-xor-v1':
            return False
        ts=certificate['terms']
        if not isinstance(ts,list): return False
        def side(rows,pivot,bit):
            if not isinstance(rows,(tuple,list)) or not rows: raise ValueError
            derived=0
            for row,ids in rows:
                if type(row) is not int or row<=0: raise ValueError
                mask,rhs=divmod(row,2)
                if mask.bit_length()>n or mask.bit_count()>3: raise ValueError
                if pivot and mask & (1<<(pivot-1)): raise ValueError
                if not isinstance(ids,list) or not ids: raise ValueError
                original=[]
                scope=mask | ((1<<(pivot-1)) if pivot else 0)
                for ix in ids:
                    if type(ix) is not int or not 0<=ix<len(cs): raise ValueError
                    c=cs[ix]
                    if any(not (scope>>(abs(l)-1)&1) for l in c): raise ValueError
                    original.append(c)
                assignment=mask
                while True:
                    point=assignment | ((1<<(pivot-1)) if pivot and bit else 0)
                    if assignment.bit_count()%2!=rhs and all(any(bool(point & (1<<(abs(l)-1)))==(l>0) for l in c) for c in original):
                        raise ValueError
                    if not assignment: break
                    assignment=(assignment-1)&mask
                derived ^= row
            return derived
        xor=0
        for term in ts:
            pivot=term['pivot']
            if type(pivot) is not int or not 0<=pivot<=n: return False
            if not pivot: row=side(term['base'],0,0)
            else:
                row=side(term['zero'],pivot,0)
                if row != side(term['one'],pivot,1): return False
            xor ^= row
        return xor==1
    except (TypeError,ValueError,KeyError,IndexError):
        return False


def split_parity_refute(n,clauses):
    cs=_raw(n,clauses)
    basis={}
    records=[]
    stats=dict(variables_examined=0,base_rows=0,common_rows=0)
    def add(row,record):
        rem,ids=_reduce(row,1<<len(records),basis)
        if rem==0:return None
        records.append(record)
        if rem==1:
            cert=dict(kind='split-xor-v1',terms=list(_selected(records,ids)))
            if not check_split_parity(n,cs,cert): raise AssertionError('invalid derived refutation')
            return dict(status='UNSAT',certificate=cert,stats=stats)
        basis[rem.bit_length()-1]=rem,ids
        return None
    for row,ids in _leaves(enumerate(cs)):
        stats['base_rows']+=1
        ans=add(row,dict(pivot=0,base=[(row,ids)]))
        if ans:return ans
    buckets=defaultdict(lambda:[[],[]])
    for ix,c in enumerate(cs):
        signs=frozenset(c)
        if any(-l in signs for l in signs): continue
        for l in signs:
            buckets[abs(l)][int(l<0)].append((ix,tuple(v for v in c if abs(v)!=abs(l))))
    for pivot,bucket in sorted(buckets.items()):
        if not all(bucket):continue
        stats['variables_examined']+=1
        for row,zero,one in _common(_leaves(bucket[0]),_leaves(bucket[1])):
            stats['common_rows']+=1
            ans=add(row,dict(pivot=pivot,zero=zero,one=one))
            if ans:return ans
    return dict(status='UNKNOWN',certificate=None,stats=stats)
