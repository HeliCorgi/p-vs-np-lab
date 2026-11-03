"""Uniform decision dispatch for explicit XOR supports; no counting is performed."""
from __future__ import annotations

from .frontier import _read_groups, decide_signature_supports
from .unit_matching import decide_unit_supports


def decide_xor_choices(supports, rhs, *, max_transitions=None):
    """Use a polynomial backend when a proved restriction applies, else frontier search.

    The transition budget limits only residual frontier branching. It does
    not bound preprocessing, polynomial matching work, or total memory/time.
    Witness choices always refer to the original support order.
    """
    if type(rhs) is not int or rhs < 0:
        raise ValueError('rhs must be a nonnegative integer.')
    if max_transitions is not None and (type(max_transitions) is not int or max_transitions < 0):
        raise ValueError('max_transitions must be None or a nonnegative integer.')
    groups = _read_groups(supports)
    if any(not g for g in groups) or all(len(g) <= 2 for g in groups):
        result = decide_signature_supports(groups, rhs, max_transitions=max_transitions)
        method = 'empty_support' if any(not g for g in groups) else 'binary_affine'
    elif all(v.bit_count() <= 1 for g in groups for v in g):
        result = decide_unit_supports(groups, rhs)
        method = 'unit_matching'
    else:
        result = decide_signature_supports(groups, rhs, max_transitions=max_transitions)
        method = 'affine_frontier'
    return dict(backend=method, **result)
