"""Optional certified SAT/UNSAT gate; UNKNOWN never decides the original CNF."""
from .modular_hull import _input,modular_hull_refute,check_modular_hull
from .cyclic_four import solve_cyclic_four,check_cyclic_four
from .trit_solver import solve_trit_affine
from .mixed_modular import mixed_modular_refute,check_field_bridge
from .modular_padding import peel,_replay,lift_after_peeling


def _check_inner(n,cs,cert):
    k=cert['kind']
    if k=='boolean-modular-hull-v1':return check_modular_hull(n,cs,cert)
    if k=='boolean-field-bridge-v1':return check_field_bridge(n,cs,cert)
    if k=='boolean-cyclic-four-v1':
        return check_cyclic_four(n,cs,dict(status='UNSAT',witness=None,certificate=cert))
    return False


def check_conservation(n,clauses,report):
    """Only a checked original Boolean word or a checked refutation can pass."""
    try:
        cs=_input(n,clauses)
        if report['status']=='SAT':
            x=report['witness']
            return (type(x) is int and x>=0 and x.bit_length()<=n and
                    all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs))
        if report['status']!='UNSAT':return False
        c=report['certificate']
        if c.get('kind')=='conservation-resolution-v1':
            reduced,_=_replay(n,cs,c['steps'])
            return _check_inner(n,reduced,c['inner'])
        return _check_inner(n,cs,c)
    except (TypeError,AttributeError,IndexError,KeyError,ValueError):return False


def solve_conservation(n,clauses,*,method='auto',bridge_width=3,max_probes=None,max_short_rows=None):
    cs=_input(n,clauses);attempts=[]
    if method not in ('auto','trit','cyclic4','hull2','hull3','mixed'):raise ValueError('unknown conservation method')
    if type(bridge_width) is not int or not 0<=bridge_width<=4:raise ValueError('bad bridge width')
    if any(v is not None and (type(v) is not int or v<0) for v in (max_probes,max_short_rows)):raise ValueError('invalid bridge budget')
    def attempt(name,rows,steps=()):
        if name=='trit':r=solve_trit_affine(n,rows)
        elif name=='cyclic4':r=solve_cyclic_four(n,rows)
        elif name in ('hull2','hull3'):r=modular_hull_refute(n,rows,prime=int(name[-1]))
        else:r=mixed_modular_refute(n,rows,bridge_width=bridge_width,max_probes=max_probes,max_short_rows=max_short_rows)
        attempts.append(dict(method=name,status=r['status'],removed=len(steps),stats=r['stats']))
        if r['status']=='UNKNOWN':return None
        cert=r.get('certificate');word=r.get('witness')
        if steps:
            if word is not None:word=lift_after_peeling(n,cs,steps,word)
            else:cert=dict(kind='conservation-resolution-v1',steps=steps,inner=cert)
        out=dict(status=r['status'],method=name,witness=word,certificate=cert,attempts=attempts)
        if not check_conservation(n,cs,out):raise AssertionError('invalid conservation result')
        return out
    if method=='auto':
        for name in ('trit','cyclic4'):
            r=attempt(name,cs)
            if r is not None:return r
        raw,steps=peel(n,cs)
        if steps:
            for name in ('trit','cyclic4'):
                r=attempt(name,raw,steps)
                if r is not None:return r
        # A zero-step peel can still remove tautologies and shift row IDs.
        # Use the unmodified input when the certificate has no peel wrapper.
        r=attempt('mixed',raw if steps else cs,steps)
    else:r=attempt(method,cs)
    return r if r is not None else dict(status='UNKNOWN',method=method,witness=None,certificate=None,attempts=attempts)
