"""Failed-value inference using checked integer certificates on restricted CNFs.

At most n units are learned.  This is an incomplete conditional refutation
procedure, not a SAT decision algorithm.  Private resolution is an optional
representation prepass; each use is replayed against the appropriate residual.
"""
from collections import Counter

from .modular_hull import _input
from .modular_padding import peel, _replay
from .integer_hull import integer_hull_refute, check_integer_hull

KIND = 'boolean-integer-probe-v1'


def _restrict(cs, units):
    known = set(units)
    return tuple(tuple(l for l in c if -l not in known)
                 for c in cs if not any(l in known for l in c))


def _check_inner(n, cs, proof):
    if not isinstance(proof, dict) or set(proof) != {'steps', 'integer'}:
        return False
    steps = proof['steps']
    if not isinstance(steps, list):
        return False
    # With zero steps, normalization can still shift the original row IDs.
    rows = _replay(n, cs, steps)[0] if steps else cs
    return check_integer_hull(n, rows, proof['integer'])


def check_integer_probe(n, clauses, cert):
    """Only raw restrictions, private-resolution replay and integer proof checks.

    The checker never searches for a value or invokes the integer eliminator.
    Each learned unit is justified using the preceding units, never itself or
    a later unit.  A terminal refutation must use only the already learned units.
    """
    try:
        cs = _input(n, clauses)
        if not isinstance(cert, dict) or cert.get('kind') != KIND:
            return False
        deductions = cert['deductions']
        if not isinstance(deductions, list) or len(deductions) > n:
            return False
        units = []
        assigned = set()
        for d in deductions:
            if not isinstance(d, dict) or set(d) != {'assume', 'proof'}:
                return False
            lit = d['assume']
            if type(lit) is not int or not 1 <= abs(lit) <= n or abs(lit) in assigned:
                return False
            # Independent restriction evaluator, deliberately separate from discovery.
            values = {abs(u): u > 0 for u in (*units, lit)}
            rows = []
            for c in cs:
                if any(abs(l) in values and values[abs(l)] == (l > 0) for l in c):
                    continue
                rows.append(tuple(l for l in c if abs(l) not in values))
            if not _check_inner(n, tuple(rows), d['proof']):
                return False
            units.append(-lit)
            assigned.add(abs(lit))
        values = {abs(u): u > 0 for u in units}
        rows = []
        for c in cs:
            if any(abs(l) in values and values[abs(l)] == (l > 0) for l in c):
                continue
            rows.append(tuple(l for l in c if abs(l) not in values))
        return _check_inner(n, tuple(rows), cert['terminal'])
    except (TypeError, ValueError, KeyError, IndexError, AttributeError):
        return False


def integer_probe_refute(n, clauses, *, max_calls=None, private_peel=True, **integer_limits):
    """Learn forced bits and repeat until a refutation, a fixed point, or a cap.

    max_calls counts all integer-oracle calls, including the original/root pass.
    max_calls=None removes this outer cap; the inner integer resource limits
    remain in effect.  Unknown or capped calls never justify a learned unit.
    Variable order uses raw occurrence counts; no selector/generator hints.
    """
    cs = _input(n, clauses)
    if max_calls is not None and (type(max_calls) is not int or max_calls < 0):
        raise ValueError('expected nonnegative integer call cap or None')
    if type(private_peel) is not bool:
        raise ValueError('private_peel must be Boolean')
    if 'scopes' in integer_limits:
        raise ValueError('conditional discovery does not accept fixed scope hints')
    units = []
    deductions = []
    stats = dict(integer_calls=0, learned_units=0, rounds=0, private_eliminations=0,
                 root_status='SKIPPED', budget_limited=False, inner_budget_limited=False,
                 certificate_moduli=[], calls=[])

    def oracle(rows):
        if max_calls is not None and stats['integer_calls'] >= max_calls:
            stats['budget_limited'] = True
            return None
        steps = []
        reduced = rows
        if private_peel:
            candidate, steps = peel(n, rows)
            if steps:
                reduced = candidate
        result = integer_hull_refute(n, reduced, **integer_limits)
        stats['integer_calls'] += 1
        stats['private_eliminations'] += len(steps)
        stats['inner_budget_limited'] |= bool(result['stats'].get('budget_limited', False))
        stats['calls'].append(dict(status=result['status'], reason=result.get('reason'),
                                   clauses=len(rows), private_steps=len(steps)))
        if result['status'] != 'UNSAT':
            return False
        proof = dict(steps=steps, integer=result['certificate'])
        if not _check_inner(n, rows, proof):
            raise AssertionError('integer probe emitted an invalid inner proof')
        stats['certificate_moduli'].append(result['certificate']['modulus'])
        return proof

    def unknown(reason):
        return dict(status='UNKNOWN', reason=reason, certificate=None, witness=None, stats=stats)

    for _ in range(n + 1):
        stats['rounds'] += 1
        residual = _restrict(cs, units)
        proof = oracle(residual)
        if stats['root_status'] == 'SKIPPED' and proof is not None:
            stats['root_status'] = 'UNSAT' if proof else 'UNKNOWN'
        if proof is None:
            return unknown('integer call cap')
        if proof:
            cert = dict(kind=KIND, deductions=deductions, terminal=proof)
            if not check_integer_probe(n, cs, cert):
                raise AssertionError('integer probe refutation did not replay')
            return dict(status='UNSAT', reason='checked conditional integer refutation',
                        certificate=cert, witness=None, stats=stats)
        freq = Counter(abs(l) for c in residual for l in c)
        learned = False
        for v in sorted(freq, key=lambda x: (-freq[x], x)):
            for lit in (-v, v):
                proof = oracle(_restrict(residual, (lit,)))
                if proof is None:
                    return unknown('integer call cap')
                if proof:
                    deductions.append(dict(assume=lit, proof=proof))
                    units.append(-lit)
                    stats['learned_units'] += 1
                    learned = True
                    break
            if learned:
                break
        if not learned:
            return unknown('no further forced value found')
    raise AssertionError('more than n distinct forced variables')


def guarded_disjunction(n_left, left, n_right, right, *, left_word=None, right_word=None):
    """Fixture only: raw width-three CNF for F_left OR F_right on disjoint bits.

    Returned selector is diagnostic metadata only; discovery never receives it.
    Each guarded width-four clause uses a private helper and two ternary clauses.
    A provided model of either arm is lifted and checked against the entire CNF.
    """
    left = _input(n_left, left)
    right = _input(n_right, right)
    selector = n_left + n_right + 1
    n = selector
    rows = []
    descriptions = []
    for cs, offset, guard in ((left, 0, selector), (right, n_left, -selector)):
        for c in cs:
            shifted = tuple((1 if l > 0 else -1) * (abs(l) + offset) for l in c)
            if len(shifted) <= 2:
                rows.append((guard, *shifted))
            else:
                n += 1
                a, b, c = shifted
                rows.extend(((guard, a, n), (-n, b, c)))
                descriptions.append((n, guard, a, b, c))
    word = None
    if left_word is not None:
        if type(left_word) is not int or left_word < 0 or left_word.bit_length() > n_left:
            raise ValueError('bad left witness')
        if not all(any(bool(left_word >> (abs(l) - 1) & 1) == (l > 0) for l in c) for c in left):
            raise ValueError('left word is not a model')
        word = left_word  # selector false, right arm disabled
    elif right_word is not None:
        if type(right_word) is not int or right_word < 0 or right_word.bit_length() > n_right:
            raise ValueError('bad right witness')
        if not all(any(bool(right_word >> (abs(l) - 1) & 1) == (l > 0) for l in c) for c in right):
            raise ValueError('right word is not a model')
        word = (right_word << n_left) | (1 << (selector - 1))
    if word is not None:
        def holds(l):
            return bool(word >> (abs(l) - 1) & 1) == (l > 0)
        for h, g, a, b, c in descriptions:
            if not (holds(g) or holds(a)):
                if not (holds(b) or holds(c)):
                    raise AssertionError('guard split has no lifted value')
                word |= 1 << (h - 1)
        if not all(any(holds(l) for l in row) for row in rows):
            raise AssertionError('invalid lifted disjunction witness')
    return n, tuple(rows), word, selector
