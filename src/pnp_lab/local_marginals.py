"""Checked level-four local distributions for proper linear 3-CNF.

The output is a feasible Sherali--Adams relaxation, never a SAT decision.
Certificates store one parity bit per raw clause.  The verifier expands every
scope of at most four variables, checks raw clause support, and compares every
one-coordinate marginal using integer arithmetic.  No floating point LP is run.
"""
from itertools import combinations
from math import comb

from .modular_hull import _input

KIND = 'linear-triple-local-marginals-v1'
LEVEL = 4
MAX_STATES = 2000000
MAX_CHECKS = 5000000


def _limits(max_states, max_checks):
    if any(type(v) is not int or v < 0 for v in (max_states, max_checks)):
        raise ValueError('invalid local marginal resource cap')


def _triple_index(cs):
    index, pairs = {}, set()
    for i, c in enumerate(cs):
        scope = tuple(sorted(map(abs, c)))
        if len(scope) != 3 or len(set(scope)) != 3:
            raise ValueError('not a proper ternary clause')
        new_pairs = set(combinations(scope, 2))
        if pairs & new_pairs:
            raise ValueError('raw triple supports are not linear')
        pairs.update(new_pairs)
        index[scope] = i
    return index


class _Cap(Exception):
    def __init__(self, stats):
        self.stats = stats


def _replay(n, cs, certificate, max_states, max_checks):
    _limits(max_states, max_checks)
    if (not isinstance(certificate, dict)
            or set(certificate) != {'kind', 'variables', 'level', 'clause_parities'}
            or certificate['kind'] != KIND
            or type(certificate['variables']) is not int or certificate['variables'] != n
            or type(certificate['level']) is not int or certificate['level'] != LEVEL):
        raise ValueError('invalid local marginal certificate header')
    parities = certificate['clause_parities']
    if (type(parities) is not list or len(parities) != len(cs)
            or any(type(p) is not int or p not in (0, 1) for p in parities)):
        raise ValueError('invalid clause parity list')
    index = _triple_index(cs)
    widths = range(min(n, LEVEL) + 1)
    stats = dict(level=LEVEL, scopes_required=sum(comb(n, w) for w in widths),
                 table_states_required=sum(comb(n, w) * (1 << w) for w in widths),
                 projection_equalities_required=sum(comb(n, w) * w * (1 << (w - 1))
                                                    for w in widths if w),
                 scopes_checked=0, table_states_checked=0, positive_states=0,
                 clause_support_checks=0, projection_equalities_checked=0,
                 complete=False, budget_limited=False)
    # Preflight before range(n), materialization, or assignment enumeration.
    if (stats['table_states_required'] > max_states
            or stats['projection_equalities_required'] > max_checks):
        stats['budget_limited'] = True
        raise _Cap(stats)
    smaller_tables = {}
    for width in widths:
        for scope in combinations(range(1, n + 1), width):
            positions = {v: j for j, v in enumerate(scope)}
            present = [index[t] for t in combinations(scope, 3) if t in index]
            if len(present) > 1:
                raise ValueError('multiple raw clauses in a small scope')
            clause_index = present[0] if present else None
            if clause_index is None:
                weights, denominator = (1,) * (1 << width), 1 << width
            else:
                mask = sum(1 << positions[abs(l)] for l in cs[clause_index])
                weights = tuple(int((word & mask).bit_count() % 2 == parities[clause_index])
                                for word in range(1 << width))
                denominator = 1 << (width - 1)
            if (denominator <= 0 or any(type(w) is not int or w < 0 for w in weights)
                    or sum(weights) != denominator):
                raise ValueError('not a normalized nonnegative distribution')
            for word, weight in enumerate(weights):
                stats['table_states_checked'] += 1
                if weight:
                    stats['positive_states'] += 1
                    for i in present:
                        stats['clause_support_checks'] += 1
                        if not any(bool(word >> positions[abs(l)] & 1) == (l > 0)
                                   for l in cs[i]):
                            raise ValueError('positive mass on a falsified raw clause')
            for deleted in range(width):
                lower = scope[:deleted] + scope[deleted + 1:]
                lower_weights, lower_denominator = smaller_tables[lower]
                for word, low_weight in enumerate(lower_weights):
                    zero = (word & ((1 << deleted) - 1)) | ((word >> deleted) << (deleted + 1))
                    mass = weights[zero] + weights[zero | (1 << deleted)]
                    if mass * lower_denominator != low_weight * denominator:
                        raise ValueError('inconsistent marginal distributions')
                    stats['projection_equalities_checked'] += 1
            stats['scopes_checked'] += 1
            if width < LEVEL:
                smaller_tables[scope] = weights, denominator
    stats['complete'] = True
    return stats


def check_local_marginals(n, clauses, certificate, *, max_states=MAX_STATES,
                          max_checks=MAX_CHECKS):
    """Independently check the compact rule by all level-four finite tables.

    False means an invalid or unverified certificate; it does not mean that
    the relaxation, or the original CNF, is infeasible.
    """
    try:
        _replay(n, _input(n, clauses), certificate, max_states, max_checks)
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, _Cap):
        return False


def linear_triple_marginals(n, clauses, *, max_states=MAX_STATES,
                            max_checks=MAX_CHECKS):
    """Return UNKNOWN for SAT, and a checked relaxation witness when applicable.

    The rule selects the parity opposite the unique falsifying tuple of each
    raw triple.  At most one triple occurs in any scope of size at most four.
    Unsupported inputs and resource exhaustion produce no certificate.
    """
    _limits(max_states, max_checks)
    cs = _input(n, clauses)
    try:
        _triple_index(cs)
    except ValueError:
        return dict(status='UNKNOWN', relaxation='UNKNOWN', certificate=None,
                    reason='input is not a proper linear 3-CNF',
                    stats=dict(level=LEVEL, complete=False, budget_limited=False))
    certificate = dict(kind=KIND, variables=n, level=LEVEL,
                       clause_parities=[(sum(l < 0 for l in c) + 1) % 2 for c in cs])
    try:
        stats = _replay(n, cs, certificate, max_states, max_checks)
    except _Cap as exc:
        return dict(status='UNKNOWN', relaxation='UNKNOWN', certificate=None,
                    reason='local marginal verification cap', stats=exc.stats)
    return dict(status='UNKNOWN', relaxation='FEASIBLE', certificate=certificate,
                reason='checked local distributions do not certify a global model', stats=stats)
