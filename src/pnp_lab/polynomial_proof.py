"""Small, independently checked Boolean polynomial-calculus traces over F2.

Proof discovery is ordinary bounded-width resolution followed by a translation.
It is NOT a complete search through bounded-degree polynomial calculus.  The
checker receives original CNF clauses and arithmetic instructions only; it does
not invoke the resolution finder or trust its intermediate clauses.
"""
from collections import Counter
from itertools import product

from .modular_hull import _input

KIND = 'boolean-polynomial-calculus-v1'
MAX_NODES = 200000
MAX_MONOMIALS = 2000000
MAX_WORK = 5000000


def _degree(p):
    return max((len(m) for m in p), default=-1)


def _limits(max_degree, max_nodes, max_monomials, max_work):
    if max_degree is not None and (type(max_degree) is not int or max_degree < 0):
        raise ValueError('invalid polynomial degree cap')
    for v in (max_nodes, max_monomials, max_work):
        if type(v) is not int or v < 0:
            raise ValueError('invalid polynomial resource cap')


def _raw_cost(c):
    # An explicit upper bound on raw clause-factor expansion visits.
    return (1 << sum(l > 0 for l in c)) * (len(c) + 1)


def _multiply(p, variable):
    out = set()
    for monomial in p:
        value = tuple(sorted(set(monomial) | {variable}))
        if value in out:
            out.remove(value)
        else:
            out.add(value)
    return frozenset(out)


def _raw_polynomial(c):
    value = frozenset({()})
    for lit in c:
        times = _multiply(value, abs(lit))
        value = value ^ times if lit > 0 else times
    return value


class _Cap(Exception):
    pass


def _checked_profile(n, cs, cert, *, max_degree, max_nodes, max_monomials, max_work):
    """Independent arithmetic replayer using counted formal products.

    Monomials are tuples of ORIGINAL variable labels rather than numeric bit
    positions.  Large unused variable identifiers cannot force a huge bitset.
    """
    _limits(max_degree, max_nodes, max_monomials, max_work)
    if (not isinstance(cert, dict)
            or set(cert) != {'kind', 'field', 'variables', 'degree', 'nodes', 'root'}
            or cert['kind'] != KIND or type(cert['field']) is not int or cert['field'] != 2
            or type(cert['variables']) is not int or cert['variables'] != n
            or type(cert['degree']) is not int or cert['degree'] < 0):
        raise ValueError('invalid polynomial certificate header')
    nodes, root = cert['nodes'], cert['root']
    if (not isinstance(nodes, list) or not nodes or len(nodes) > max_nodes
            or type(root) is not int or root != len(nodes) - 1):
        raise ValueError('invalid polynomial node list')
    polys = []
    work = 0
    volume = 0
    charged_degree = 0
    peak = 0
    operations = Counter()

    def parent(j, before):
        if type(j) is not int or not 0 <= j < before:
            raise ValueError('polynomial parent is not earlier')
        return polys[j]

    for index, node in enumerate(nodes):
        if not isinstance(node, dict):
            raise ValueError('invalid polynomial node')
        tag = node.get('op')
        counts = Counter()
        if tag == 'input' and set(node) == {'op', 'clause'}:
            i = node['clause']
            if type(i) is not int or not 0 <= i < len(cs):
                raise ValueError('invalid raw clause index')
            c = cs[i]
            work += _raw_cost(c)
            if work > max_work:
                raise _Cap('polynomial work cap')
            positives = [l for l in c if l > 0]
            negatives = {abs(l) for l in c if l < 0}
            # Choose either 1 or x from each positive-literal falsity factor.
            # Repeated variables and tautologies cancel by parity, not by a
            # call to the discovery expander.
            for bits in product((False, True), repeat=len(positives)):
                monomial = tuple(sorted(negatives | {v for v, bit in zip(positives, bits) if bit}))
                counts[monomial] += 1
            p = frozenset(m for m, coefficient in counts.items() if coefficient % 2)
            step_degree = max(0, _degree(p))
        elif tag == 'add' and set(node) == {'op', 'left', 'right'}:
            a = parent(node['left'], index)
            b = parent(node['right'], index)
            work += len(a) + len(b)
            if work > max_work:
                raise _Cap('polynomial work cap')
            counts.update(a)
            counts.update(b)
            p = frozenset(m for m, coefficient in counts.items() if coefficient % 2)
            step_degree = max(0, _degree(p))
        elif tag == 'multiply' and set(node) == {'op', 'parent', 'variable'}:
            a = parent(node['parent'], index)
            v = node['variable']
            if type(v) is not int or not 1 <= v <= n:
                raise ValueError('invalid multiplication variable')
            work += sum(len(m) + 1 for m in a)
            if work > max_work:
                raise _Cap('polynomial work cap')
            # Charge before Boolean reduction, including a repeated variable.
            step_degree = max(0, _degree(a) + 1)
            for m in a:
                counts[tuple(sorted((*m, v))) if v not in m else m] += 1
            p = frozenset(m for m, coefficient in counts.items() if coefficient % 2)
        else:
            raise ValueError('invalid polynomial operation')
        charged_degree = max(charged_degree, step_degree)
        volume += len(p)
        peak = max(peak, len(p))
        if max_degree is not None and charged_degree > max_degree:
            raise _Cap('polynomial degree cap')
        if volume > max_monomials:
            raise _Cap('polynomial monomial cap')
        operations[tag] += 1
        polys.append(p)
    if cert['degree'] != charged_degree or polys[root] != frozenset({()}):
        raise ValueError('wrong degree claim or no final constant-one contradiction')
    return dict(proof_nodes=len(nodes), proof_degree=charged_degree,
                proof_monomial_occurrences=volume, max_polynomial_monomials=peak,
                proof_work=work, proof_operations=dict(sorted(operations.items())))


def check_polynomial_proof(n, clauses, cert, *, max_degree=None, max_nodes=MAX_NODES,
                           max_monomials=MAX_MONOMIALS, max_work=MAX_WORK):
    """Check every arithmetic instruction and the final 1, against raw clauses.

    Caps reject a proof; their exhaustion never certifies the original CNF.
    Multiplication is in the Boolean quotient, with the unreduced degree cost
    of multiplying the current multilinear representative by a variable.
    """
    try:
        _checked_profile(n, _input(n, clauses), cert, max_degree=max_degree,
                         max_nodes=max_nodes, max_monomials=max_monomials, max_work=max_work)
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, _Cap):
        return False


def resolution_to_polynomial(n, clauses, certificate, *, max_degree=None,
                            max_nodes=MAX_NODES, max_monomials=MAX_MONOMIALS,
                            max_work=MAX_WORK):
    """Translate one checked resolution DAG to an explicit F2 arithmetic DAG.

    Resolving (x OR A) and (not x OR B) uses only the false-literal factors
    missing from the other parent.  Shared factors are never squared.  Every
    intermediate product uses at most the resolvent variables plus the pivot.
    The output consequently has charged degree at most source width + 1.
    """
    from .resolution_closure import ResolutionReplayLimit, replay_resolution
    cs = _input(n, clauses)
    _limits(max_degree, max_nodes, max_monomials, max_work)
    source_nodes = certificate.get('nodes') if isinstance(certificate, dict) else None
    source_width = certificate.get('width') if isinstance(certificate, dict) else None
    stats = dict(source_resolution_nodes=len(source_nodes) if isinstance(source_nodes, list) else 0,
                 source_resolution_width=source_width if type(source_width) is int else 0, generated_nodes=0,
                 generated_monomial_occurrences=0, generated_work=0,
                 max_generated_degree=0, budget_limited=False)
    try:
        source_rows = replay_resolution(n, cs, certificate, max_nodes=max_nodes,
                                        max_width=max_degree, max_literal_occurrences=max_work)
    except ResolutionReplayLimit as cap:
        stats['budget_limited'] = True
        return dict(status='UNKNOWN', reason=str(cap), certificate=None, witness=None, stats=stats)
    except (ValueError, TypeError, KeyError, IndexError, AttributeError) as exc:
        raise ValueError('invalid source resolution certificate') from exc
    nodes = []
    polynomials = []
    memo = {}
    targets = []

    def reserve(cost, charged):
        if stats['generated_work'] + cost > max_work:
            raise _Cap('polynomial work cap')
        if len(nodes) >= max_nodes:
            raise _Cap('polynomial node cap')
        if max_degree is not None and charged > max_degree:
            raise _Cap('polynomial degree cap')
        stats['generated_work'] += cost
        stats['max_generated_degree'] = max(stats['max_generated_degree'], charged)

    def emit(key, node, poly):
        stats['generated_monomial_occurrences'] += len(poly)
        if stats['generated_monomial_occurrences'] > max_monomials:
            raise _Cap('polynomial monomial cap')
        i = len(nodes)
        memo[key] = i
        nodes.append(node)
        polynomials.append(poly)
        stats['generated_nodes'] = len(nodes)
        return i

    def raw(i):
        key = ('input', i)
        if key in memo:
            return memo[key]
        p = _raw_polynomial(cs[i])
        reserve(_raw_cost(cs[i]), max(0, _degree(p)))
        return emit(key, dict(op='input', clause=i), p)

    def add(i, j):
        i, j = sorted((i, j))
        key = ('add', i, j)
        if key in memo:
            return memo[key]
        a, b = polynomials[i], polynomials[j]
        reserve(len(a) + len(b), max(0, _degree(a), _degree(b)))
        p = a ^ b
        return emit(key, dict(op='add', left=i, right=j), p)

    def multiply(i, v):
        key = ('multiply', i, v)
        if key in memo:
            return memo[key]
        a = polynomials[i]
        reserve(sum(len(m) + 1 for m in a), max(0, _degree(a) + 1))
        p = _multiply(a, v)
        return emit(key, dict(op='multiply', parent=i, variable=v), p)

    def false_factor(i, literal):
        times = multiply(i, abs(literal))
        return add(i, times) if literal > 0 else times

    try:
        for source_index, step in enumerate(certificate['nodes']):
            c = source_rows[source_index]
            if step['op'] == 'input':
                target = raw(step['clause'])
            else:
                left, right, pivot = step['left'], step['right'], step['pivot']
                a = source_rows[left] - {pivot}
                b = source_rows[right] - {-pivot}
                first, second = targets[left], targets[right]
                for literal in sorted(b - a, key=lambda l: (abs(l), l)):
                    first = false_factor(first, literal)
                for literal in sorted(a - b, key=lambda l: (abs(l), l)):
                    second = false_factor(second, literal)
                target = add(first, second)
            # This inexpensive translation assertion is NOT trusted by the
            # final checker, which receives no resolution parents or clauses.
            if polynomials[target] != _raw_polynomial(tuple(sorted(c))):
                raise AssertionError('resolution-to-polynomial identity failed')
            targets.append(target)
    except _Cap as cap:
        stats['budget_limited'] = True
        return dict(status='UNKNOWN', reason=str(cap), certificate=None, witness=None, stats=stats)

    root = targets[certificate['root']]
    needed = set()
    todo = [root]
    while todo:
        i = todo.pop()
        if i in needed:
            continue
        needed.add(i)
        node = nodes[i]
        if node['op'] == 'add':
            todo.extend((node['left'], node['right']))
        elif node['op'] == 'multiply':
            todo.append(node['parent'])
    order = sorted(needed)
    names = {old: new for new, old in enumerate(order)}
    compact = []
    degree = 0
    for i in order:
        node = nodes[i].copy()
        if node['op'] == 'add':
            node['left'], node['right'] = names[node['left']], names[node['right']]
            degree = max(degree, _degree(polynomials[i]))
        elif node['op'] == 'multiply':
            degree = max(degree, _degree(polynomials[node['parent']]) + 1)
            node['parent'] = names[node['parent']]
        else:
            degree = max(degree, _degree(polynomials[i]))
        compact.append(node)
    cert = dict(kind=KIND, field=2, variables=n, degree=degree,
                nodes=compact, root=names[root])
    profile = _checked_profile(n, cs, cert, max_degree=max_degree,
                               max_nodes=max_nodes, max_monomials=max_monomials, max_work=max_work)
    stats.update(profile)
    if degree > certificate['width'] + 1:
        raise AssertionError('translation exceeded the stated degree bound')
    return dict(status='UNSAT', reason='checked Boolean polynomial-calculus contradiction',
                certificate=cert, witness=None, stats=stats)


def polynomial_refute(n, clauses, *, width=4, max_rows=50000, max_pairs=1000000,
                      max_degree=None, max_nodes=MAX_NODES,
                      max_monomials=MAX_MONOMIALS, max_work=MAX_WORK):
    """Resolution-guided proof discovery; UNKNOWN is never a degree lower bound."""
    from .resolution_closure import resolution_refute
    cs = _input(n, clauses)
    _limits(max_degree, max_nodes, max_monomials, max_work)
    result = resolution_refute(n, cs, width=width, max_rows=max_rows, max_pairs=max_pairs)
    if result['status'] != 'UNSAT':
        return dict(status='UNKNOWN', reason='resolution guide did not refute', certificate=None,
                    witness=None, stats=dict(resolution=result['stats'], budget_limited=result['stats'].get('budget_limited', False)))
    answer = resolution_to_polynomial(n, cs, result['certificate'], max_degree=max_degree,
                                      max_nodes=max_nodes, max_monomials=max_monomials, max_work=max_work)
    answer['stats']['resolution'] = result['stats']
    return answer
