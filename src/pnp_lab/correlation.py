"""Explicit entry point for checked nonlinear correlations on raw 3-CNF.

Discovery is bounded ordinary resolution; the other proof representations
change independent replay, not its search power. Local marginals are a
separate relaxation diagnostic and can never establish SAT.
"""
from .local_marginals import (KIND as MARGINAL_KIND, check_local_marginals,
                              linear_triple_marginals)
from .polynomial_proof import (KIND as POLYNOMIAL_KIND, check_polynomial_proof,
                               resolution_to_polynomial)
from .relation_proof import (KIND as RELATION_KIND, check_relation_proof,
                             resolution_to_relations)
from .resolution_closure import (KIND as RESOLUTION_KIND, check_resolution,
                                 check_width_closure, resolution_refute)


def solve_correlations(n, clauses, *, method='relations', width=4,
                       max_rows=50000, max_pairs=1000000, max_subsets=5000000,
                       max_union_width=12, max_degree=None):
    """Return a checked refutation or UNKNOWN, with full guide-search statistics."""
    from .modular_hull import _input
    cs = _input(n, clauses)
    if method == 'marginals':
        return linear_triple_marginals(n, cs)
    if method not in ('resolution', 'relations', 'polynomial'):
        raise ValueError('unknown correlation method')
    source = resolution_refute(n, cs, width=width, max_rows=max_rows,
                               max_pairs=max_pairs, max_subsets=max_subsets)
    if method == 'resolution' or source['status'] != 'UNSAT':
        return source
    if method == 'relations':
        result = resolution_to_relations(n, cs, source['certificate'],
                                          max_union_width=max_union_width)
    else:
        result = resolution_to_polynomial(n, cs, source['certificate'],
                                          max_degree=max_degree)
    result['stats']['resolution_search'] = source['stats']
    return result


def check_correlation_report(n, clauses, report):
    """Return a precise verified statement, or None; never promote UNKNOWN to SAT."""
    if not isinstance(report, dict):
        return None
    cert = report.get('certificate')
    if report.get('status') == 'UNSAT' and isinstance(cert, dict):
        if not isinstance(cert.get('kind'), str):
            return None
        checker = {RESOLUTION_KIND: check_resolution,
                   RELATION_KIND: check_relation_proof,
                   POLYNOMIAL_KIND: check_polynomial_proof}.get(cert.get('kind'))
        if checker is not None and checker(n, clauses, cert):
            return 'original CNF is UNSAT'
    if report.get('status') == 'UNKNOWN':
        if (isinstance(cert, dict) and cert.get('kind') == MARGINAL_KIND
                and report.get('relaxation') == 'FEASIBLE'
                and check_local_marginals(n, clauses, cert)):
            return 'level-4 local distributions are feasible; original CNF is undecided'
        closure = report.get('closure_certificate')
        if isinstance(closure, dict) and check_width_closure(n, clauses, closure):
            return ('no ordinary resolution refutation of width <= '
                    + str(closure['width']) + '; original CNF is undecided')
    return None
