"""Verify the recovered core and bind its independently checked contradiction to the input."""
from .case_parity import case_parity_refute,check_case_parity
from .blind_recovery import recover_blind,check_recovery
from .split_parity import split_parity_refute,check_split_parity


def check_recovered_parity(n,clauses,cert):
    try:
        if not isinstance(cert,dict) or cert.get('kind') not in ('recovered-parity-v1','recovered-case-parity-v1'):return False
        rr=cert['reduction']
        if not check_recovery(n,clauses,rr):return False
        if rr['status']=='UNSAT':return cert['inner'] is None
        checker=check_case_parity if cert['kind']=='recovered-case-parity-v1' else check_split_parity
        return rr['status']=='OPEN' and checker(rr['n_reduced'],rr['clauses'],cert['inner'])
    except (KeyError,ValueError,IndexError,TypeError):return False


def recover_then_refute(n,clauses,*,case=False):
    if type(case) is not bool:raise ValueError("case must be Boolean")
    cs=tuple(tuple(c) for c in clauses);rr=recover_blind(n,cs)
    proof=None
    stats=dict(core_status=rr['status'],core_variables=rr['n_reduced'],core_clauses=len(rr['clauses']))
    if rr['status']=='OPEN':
        inner=(case_parity_refute if case else split_parity_refute)(rr['n_reduced'],rr['clauses'])
        stats['inner_stats']=inner['stats'];proof=inner['certificate']
    if rr['status']=='UNSAT' or proof is not None:
        cert=dict(kind='recovered-case-parity-v1' if case else 'recovered-parity-v1',reduction=rr,inner=proof)
        if not check_recovered_parity(n,cs,cert):raise AssertionError('invalid composed refutation')
        return dict(status='UNSAT',certificate=cert,stats=stats)
    return dict(status='UNKNOWN',certificate=None,stats=stats)
