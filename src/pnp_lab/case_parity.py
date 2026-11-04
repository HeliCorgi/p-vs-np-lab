"""One additional binary split with two independently checked private/parity refutations."""
from collections import Counter

from .private_resolution import _input,private_parity_refute,check_private_parity

KIND='binary-case-private-parity-v1'


def _residual(cs,true_lit):
    # Keep row order and remaining literal order so inner proof clause IDs
    # are reproducible. No deduplication or coordinate renumbering here.
    return tuple(tuple(l for l in c if l!=-true_lit) for c in cs if true_lit not in c)


def check_case_parity(n,clauses,cert):
    """Replay the split certificate against both restrictions of this original input."""
    try:
        raw=_input(n,clauses)
        if not isinstance(cert,dict) or cert['kind']!=KIND:return False
        if cert['mode']=='root':return check_private_parity(n,raw,cert['proof'])
        if cert['mode']!='both':return False
        pivot=cert['pivot']
        if type(pivot) is not int or not 1<=pivot<=n:return False
        for bit,field in ((False,'zero'),(True,'one')):
            rows=[]
            for c in raw:
                if any(abs(l)==pivot and (l>0)==bit for l in c):continue
                rows.append(tuple(l for l in c if abs(l)!=pivot))
            if not check_private_parity(n,rows,cert[field]):return False
        return True
    except (TypeError,ValueError,KeyError,AttributeError,IndexError):return False


def case_parity_refute(n,clauses,*,max_pivots=None,try_root=True):
    """Find an original refutation or both children of one cut. UNKNOWN is inconclusive.

    A pivot budget caps distinct outer candidates tried. It does not cap
    subcall time or inner Gaussian/conditional work. try_root bypasses only
    the original-formula prepass and never nests another call to this finder.
    """
    cs=_input(n,clauses)
    if type(try_root) is not bool:raise ValueError('try_root must be Boolean')
    if max_pivots is not None and (type(max_pivots) is not int or max_pivots<0):
        raise ValueError('expected nonnegative pivot cap or None')
    freq=Counter(abs(l) for c in cs for l in c)
    stats=dict(candidate_pivots=len(freq),pivots_tried=0,inner_calls=0,root_status='SKIPPED',
               branch_unsat_proofs=0,successful_pivot=None,limit_reached=False)
    def checked(cert):
        if not check_case_parity(n,cs,cert):raise AssertionError('invalid composed parity proof')
        return dict(status='UNSAT',certificate=cert,stats=stats)
    if try_root:
        stats['inner_calls']+=1
        r=private_parity_refute(n,cs)
        stats['root_status']=r['status']
        if r['status']=='UNSAT':
            return checked(dict(kind=KIND,mode='root',proof=r['certificate']))
    for v in sorted(freq,key=lambda i:(-freq[i],i)):
        if max_pivots is not None and stats['pivots_tried']>=max_pivots:
            stats['limit_reached']=True;break
        stats['pivots_tried']+=1;proofs=[]
        for lit in (-v,v):
            stats['inner_calls']+=1
            r=private_parity_refute(n,_residual(cs,lit))
            if r['status']!='UNSAT':break
            stats['branch_unsat_proofs']+=1;proofs.append(r['certificate'])
        if len(proofs)==2:
            stats['successful_pivot']=v
            return checked(dict(kind=KIND,mode='both',pivot=v,zero=proofs[0],one=proofs[1]))
    return dict(status='UNKNOWN',certificate=None,stats=stats)
