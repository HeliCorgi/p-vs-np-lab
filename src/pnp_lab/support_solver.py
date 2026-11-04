"""Exact dispatch for explicitly listed XOR supports; optional recognizers can abstain."""
from __future__ import annotations

from .frontier import _affine_core, _read_groups, decide_signature_supports
from .gauge_matching import decide_with_gauge_matching, radius_one_center
from .graphic_support import decide_graphic_supports
from .unit_matching import decide_unit_supports


def decide_xor_choices(supports, rhs, *, max_transitions=None, method='auto',
                       max_matching_calls=None, max_outer_branches=None,
                       max_tree_trials=3, cmr_executable='cmr-graphic'):
    """Return a checked choice per original group on SAT. No exact counts.

    Auto tries polynomial special cases and a bounded search for a graph
    representation, and falls back on complete frontier search. `gauge` can
    branch exponentially; matching/outer budgets apply there, not to other
    methods. The transition budget applies to frontier transitions only.
    `graphic`, `holes`, and optional `cmr` deliberately return UNKNOWN on an
    unrecognized residual, never a false UNSAT. CMR runs only on request.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError('rhs must be a nonnegative integer.')
    if method not in ('auto','frontier','gauge','graphic','cmr','holes'):
        raise ValueError('Unknown support decision method.')
    for name,budget in [('max_transitions',max_transitions),('max_matching_calls',max_matching_calls),
                        ('max_outer_branches',max_outer_branches),('max_tree_trials',max_tree_trials)]:
        if budget is not None and (type(budget) is not int or budget < 0):
            raise ValueError(f'{name} must be a nonnegative integer.')
    if max_tree_trials is None:
        raise ValueError('max_tree_trials must be finite.')
    gs = _read_groups(supports)
    if method=='gauge':
        return dict(backend='gauge_branch_matching',**decide_with_gauge_matching(
            gs,rhs,max_matching_calls=max_matching_calls,max_outer_branches=max_outer_branches))
    if method=='frontier' or any(not g for g in gs) or (method=='auto' and all(len(g)<=2 for g in gs)):
        name='empty_support' if any(not g for g in gs) else ('binary_affine' if method=='auto' else 'affine_frontier')
        return dict(backend=name,**decide_signature_supports(gs,rhs,max_transitions=max_transitions))
    if method=='auto' and all(v.bit_count()<=1 for g in gs for v in g):
        return dict(backend='unit_matching',**decide_unit_supports(gs,rhs))
    if method=='auto' and all(radius_one_center(g) is not None for g in gs):
        return dict(backend='translated_unit_matching',**decide_with_gauge_matching(gs,rhs,max_matching_calls=1))
    if method=='holes':
        from .hole_flats import decide_hole_flats
        return dict(backend='hole_flats',**decide_hole_flats(gs,rhs,cover=True))
    core = _affine_core(gs,rhs)
    def lifted(backend, answer):
        # Retain certificate alongside the coordinate domain it belongs to.
        # Projected support/target can be regenerated with affine_core(gs,rhs).
        return dict(backend=backend,status=answer['status'],reason=answer.get('reason'),
                    witness=core.lift(answer['witness']) if answer['status']=='SAT' else None,
                    certificate_domain='affine_core(supports,rhs)',absorbed_groups=len(core.absorbed),
                    absorbed_rank=len(core.basis),residual_groups=len(core.residual),residual=answer)
    vals,t = core.supports,core.target
    if method=='cmr':
        from .cmr_graphic import decide_with_cmr
        return lifted('cmr_graphic_matching',decide_with_cmr(vals,t,executable=cmr_executable))
    if method=='graphic':
        return lifted('graphic_matching',decide_graphic_supports(vals,t,max_tree_trials=max_tree_trials))
    if all(radius_one_center(g) is not None for g in vals):
        return lifted('residual_unit_matching',decide_with_gauge_matching(vals,t,max_matching_calls=1))
    if all(len(g)<=3 for g in vals):
        graph = decide_graphic_supports(vals,t,max_tree_trials=max_tree_trials)
        if graph['status']!='UNKNOWN':
            return lifted('graphic_matching',graph)
        from .hole_flats import decide_hole_flats
        holes = decide_hole_flats(vals,t,cover=True)
        if holes['status']!='UNKNOWN':
            return lifted('hole_flats',holes)
    return lifted('affine_frontier',decide_signature_supports(vals,t,max_transitions=max_transitions))
