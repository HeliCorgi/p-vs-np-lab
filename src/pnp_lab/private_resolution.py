"""Derive a single layer of short resolvents, then use certified split parity.

Original signed row indices are never renumbered. A newly derived row is
assigned index m+j and may be used only by the nested parity proof, not as
a resolution premise in this pass. This is a polynomial, incomplete UNSAT
refuter. Appending the implications preserves the full model set.
"""
from __future__ import annotations

from collections import defaultdict
from .split_parity import split_parity_refute, check_split_parity

KIND = 'private-resolution-parity-v1'


def _input(n, clauses):
    if type(n) is not int or n<0 or isinstance(clauses,(str,bytes)):
        raise ValueError('Expected a nonnegative scope and signed 3-CNF.')
    rows=[]
    try:
        for c in clauses:
            if isinstance(c,(str,bytes)):raise ValueError('Invalid clause.')
            c=tuple(c)
            if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):
                raise ValueError('Invalid signed width-three clause.')
            rows.append(c)
    except TypeError as e:
        raise ValueError('Expected an iterable of clauses.') from e
    return tuple(rows)


def check_private_parity(n, clauses, cert):
    """Replay the supplied resolution steps and then the separate parity certificate.

    Local checks justify any ordered subset of the allowed derivations,
    without trusting enumeration, private helper names, or the finder.
    """
    try:
        raw=_input(n,clauses)
        if not isinstance(cert,dict) or cert['kind']!=KIND:return False
        steps=cert['resolution']
        if not isinstance(steps,list) or len(steps)>n:return False
        seen={frozenset(c) for c in raw}
        rows=list(raw)
        last=0
        for st in steps:
            p,a,b,j=(st[k] for k in ('pivot','positive_parent','negative_parent','id'))
            if (any(type(x) is not int for x in (p,a,b,j)) or not last<p<=n or
                    j!=len(rows) or not 0<=a<len(raw) or not 0<=b<len(raw) or a==b):
                return False
            last=p
            s=st['clause']
            if (not isinstance(s,list) or len(s)>3 or
                    any(type(l) is not int or not 1<=abs(l)<=n for l in s)):
                return False
            # Independent, intentionally literal test of the premise convention.
            if (p not in raw[a] or -p not in raw[b] or
                    sum(c.count(p) for c in raw)!=1 or sum(c.count(-p) for c in raw)!=1):
                return False
            joined=(set(raw[a])-{p})|(set(raw[b])-{-p})
            if (p in joined or -p in joined or any(-l in joined for l in joined) or
                    s!=sorted(joined,key=abs) or frozenset(s) in seen):
                return False
            seen.add(frozenset(s));rows.append(tuple(s))
        return check_split_parity(n,rows,cert['parity'])
    except (TypeError,ValueError,KeyError,IndexError):
        return False


def private_parity_refute(n,clauses):
    """Search one simultaneous polynomial pass; UNKNOWN is not a SAT decision."""
    cs=_input(n,clauses)
    occ=defaultdict(list)
    for i,row in enumerate(cs):
        for lit in row:occ[lit].append(i)
    seen={frozenset(c) for c in cs}; augmented=list(cs);steps=[];eligible=0
    for p in sorted(l for l in occ if l>0):
        if len(occ[p])!=1 or len(occ.get(-p,()))!=1:continue
        i,j=occ[p][0],occ[-p][0]
        if i==j:continue
        eligible+=1
        re=frozenset([l for l in cs[i] if l!=p]+[l for l in cs[j] if l!=-p])
        if re in seen or len(re)>3 or any(-l in re for l in re):continue
        row=tuple(sorted(re,key=abs));seen.add(re)
        steps.append(dict(pivot=p,positive_parent=i,negative_parent=j,id=len(augmented),clause=list(row)))
        augmented.append(row)
    inner=split_parity_refute(n,augmented)
    stats=dict(candidate_variables=eligible,resolvents_added=len(steps),split_stats=inner['stats'])
    if inner['status']!='UNSAT':return dict(status='UNKNOWN',certificate=None,stats=stats)
    cert=dict(kind=KIND,resolution=steps,parity=inner['certificate'])
    if not check_private_parity(n,cs,cert):raise AssertionError('Invalid resolved-parity certificate.')
    return dict(status='UNSAT',certificate=cert,stats=stats)
