"""Finite audit of the common-annihilator simulation for affine-clause DAGs.

This module is deliberately bounded.  It validates semantic inferences on the
whole small Boolean cube and exports actual ordinary F2 polynomial-calculus
traces.  It is neither a general SAT solver nor an efficient proof finder.
All repeated powers survive until explicit Boolean axiom steps remove them.
"""
from itertools import product

from .parity_pc import (ONE, ZERO, MAX_NODES, MAX_MONOMIALS, _Builder,
                        _degree, replay_parity_pc)
from .parity_query import _input


DAG_KIND = 'semantic-affine-dag-v1'
MAX_ASSIGNMENTS = 4096
MAX_SEMANTIC_WORK = 1000000
MAX_PRODUCT_PAIRS = 2000000
MAX_MASK_DEGREE = 64


def poly_mul(left, right):
    if len(left) * len(right) > MAX_PRODUCT_PAIRS:
        raise ValueError('finite sparse-product pair cap')
    result = set()
    for a in left:
        for b in right:
            monomial = tuple(sorted((*a, *b)))
            if monomial in result:
                result.remove(monomial)
            else:
                result.add(monomial)
    return frozenset(result)


def squarefree(polynomial):
    result = set()
    for monomial in polynomial:
        reduced = tuple(sorted(set(monomial)))
        if reduced in result:
            result.remove(reduced)
        else:
            result.add(reduced)
    return frozenset(result)


def _poly(n, value):
    if not isinstance(value, (list, tuple, set, frozenset)):
        raise ValueError('invalid polynomial')
    out = []
    for monomial in value:
        if (not isinstance(monomial, (list, tuple))
                or len(monomial) > MAX_MASK_DEGREE
                or any(type(v) is not int or not 1 <= v <= n for v in monomial)
                or list(monomial) != sorted(monomial)):
            raise ValueError('invalid ordinary monomial')
        out.append(tuple(monomial))
    if len(set(out)) != len(out):
        raise ValueError('duplicate polynomial term')
    return frozenset(out)


def _eval(polynomial, assignment):
    value = 0
    for monomial in polynomial:
        value ^= int(all(assignment[v - 1] for v in monomial))
    return value


def _clause(n, clause):
    if not isinstance(clause, (tuple, list)):
        raise ValueError('invalid affine clause')
    out = []
    for literal in clause:
        if (not isinstance(literal, (tuple, list)) or len(literal) != 2
                or not isinstance(literal[0], (tuple, list))
                or type(literal[1]) is not int or literal[1] not in (0, 1)
                or any(type(v) is not int or not 1 <= v <= n for v in literal[0])
                or list(literal[0]) != sorted(set(literal[0]))):
            raise ValueError('invalid affine literal')
        out.append((tuple(literal[0]), literal[1]))
    return tuple(out)


def raw_affine_clause(clause):
    """The affine literal is true at value one; negative x means 1+x."""
    return tuple(((abs(v),), int(v < 0)) for v in clause)


def _holds(clause, assignment):
    for scope, constant in clause:
        value = constant
        for v in scope:
            value ^= assignment[v - 1]
        if value:
            return True
    return False


def clause_indicator(n, clause):
    """Return a rank-degree ordinary polynomial for the falsity flat.

    An inconsistent falsity system is a tautological clause: its indicator is
    zero and its rank is None, rather than a spurious codimension-zero flat.
    Gaussian elimination is used only to select an equivalent affine basis.
    """
    _input(n, ())
    clause = _clause(n, clause)
    basis = {}
    for scope, constant in clause:
        row = sum(1 << (v - 1) for v in scope)
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (row, constant)
                break
            old, rhs = basis[pivot]
            row ^= old
            constant ^= rhs
        else:
            if constant:
                return dict(rank=None, polynomial=ZERO, equations=())
    value = ONE
    equations = []
    for pivot in sorted(basis):
        row, constant = basis[pivot]
        scope = tuple(i + 1 for i in range(n) if row >> i & 1)
        equations.append((scope, constant))
        affine = frozenset((v,) for v in scope) ^ (ONE if constant else ZERO)
        value = poly_mul(value, ONE ^ affine)
    return dict(rank=len(basis), polynomial=value, equations=tuple(equations))


def replay_affine_dag(n, clauses, certificate, *, max_assignments=MAX_ASSIGNMENTS,
                      max_semantic_work=MAX_SEMANTIC_WORK):
    """Check raw inputs, each binary/unary inference, and the empty last line.

    Parents may be reused.  This checker uses truth tables, independently of
    the Gaussian rank computation used by the algebraic converter.
    """
    raw = _input(n, clauses)
    if any(len({abs(v) for v in c}) != len(c) for c in raw):
        raise ValueError('this audit requires proper raw clauses')
    if any(type(cap) is not int or cap < 0 for cap in
           (max_assignments, max_semantic_work)):
        raise ValueError('invalid semantic audit cap')
    if n >= max_assignments.bit_length() or (1 << n) > max_assignments:
        raise ValueError('finite semantic assignment cap')
    if (type(certificate) is not dict
            or set(certificate) != {'kind', 'variables', 'nodes'}
            or certificate['kind'] != DAG_KIND
            or type(certificate['variables']) is not int
            or certificate['variables'] != n
            or type(certificate['nodes']) is not list
            or not certificate['nodes']):
        raise ValueError('invalid affine DAG')
    nodes = certificate['nodes']
    if len(nodes) * (1 << n) > max_semantic_work:
        raise ValueError('finite semantic work cap')
    parsed, truth, uses = [], [], [0] * len(nodes)
    assignments = tuple(product((0, 1), repeat=n))
    all_bits = (1 << len(assignments)) - 1
    checked = work = 0
    for ix, node in enumerate(nodes):
        if type(node) is not dict:
            raise ValueError('invalid affine DAG node')
        tag = node.get('op')
        expected = {'op', 'clause', 'input'} if tag == 'input' else {'op', 'clause', 'parents'}
        if set(node) != expected or tag not in ('input', 'infer'):
            raise ValueError('invalid affine DAG operation')
        clause = _clause(n, node['clause'])
        work += len(assignments) * (1 + sum(1 + len(scope) for scope, _ in clause))
        if work > max_semantic_work:
            raise ValueError('finite semantic literal-work cap')
        values = 0
        for j, assignment in enumerate(assignments):
            if _holds(clause, assignment):
                values |= 1 << j
        if tag == 'input':
            index = node['input']
            if type(index) is not int or not 0 <= index < len(raw):
                raise ValueError('invalid raw input index')
            if sorted(clause) != sorted(raw_affine_clause(raw[index])):
                raise ValueError('affine input does not equal the cited raw clause')
        else:
            parents = node['parents']
            if (not isinstance(parents, (list, tuple)) or len(parents) not in (1, 2)
                    or any(type(p) is not int or not 0 <= p < ix for p in parents)):
                raise ValueError('invalid affine DAG parent')
            joint = all_bits
            for parent in parents:
                uses[parent] += 1
                joint &= truth[parent]
            if joint & (all_bits ^ values):
                raise ValueError('unsound affine semantic inference')
            checked += len(assignments)
        parsed.append(clause)
        truth.append(values)
    if parsed[-1] != ():
        raise ValueError('affine DAG must end with the actual empty clause')
    return dict(raw=raw, clauses=tuple(parsed), truth=tuple(truth),
                assignments=assignments,
                profile=dict(dag_nodes=len(nodes), assignment_checks=checked,
                             semantic_literal_work=work,
                             shared_nodes=sum(count > 1 for count in uses),
                             max_parent_reuses=max(uses)))


def _times(builder, parent, polynomial):
    terms = []
    for monomial in sorted(polynomial):
        node = parent
        for variable in monomial:
            node = builder.multiply(node, variable)
        terms.append(node)
    return builder.sum(terms)


def _boolean_zero(builder, polynomial):
    """Prove p from Boolean axioms at degree deg p, if p vanishes on the cube."""
    if squarefree(polynomial):
        raise ValueError('polynomial is not identically zero on the Boolean cube')
    terms = []
    for monomial in sorted(polynomial):
        current = list(monomial)
        while len(set(current)) != len(current):
            variable = next(v for i, v in enumerate(current[1:], 1) if current[i-1] == v)
            quotient = current.copy()
            quotient.remove(variable)
            quotient.remove(variable)
            node = builder.boolean(variable)
            for v in quotient:
                node = builder.multiply(node, v)
            terms.append(node)
            current.remove(variable)
    root = builder.sum(terms)
    if builder.polynomials[root] != polynomial:
        raise AssertionError('Boolean-ideal telescoping identity failed')
    return root


def boolean_zero_pc(n, polynomial, *, max_nodes=MAX_NODES,
                    max_monomials=MAX_MONOMIALS):
    """Export a genuine ordinary-PC proof of a Boolean-zero polynomial."""
    _input(n, ())
    value = _poly(n, polynomial)
    builder = _Builder(n, (), (), max_nodes, max_monomials)
    proof = builder.export(_boolean_zero(builder, value))
    replay = replay_parity_pc(n, (), proof, max_degree=_degree(value),
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if replay['root'] != value:
        raise AssertionError('Boolean-ideal proof replay disagrees')
    return proof


def masked_affine_dag_pc(n, clauses, certificate, mask, rank_limit, *,
                         max_assignments=MAX_ASSIGNMENTS,
                         max_semantic_work=MAX_SEMANTIC_WORK,
                         max_nodes=MAX_NODES, max_monomials=MAX_MONOMIALS):
    """Derive f from F, when f vanishes on every discarded high-rank flat.

    The final ordinary degree is at most deg(f)+3*rank_limit.  A nonzero f
    is a consequence, not usually a refutation.  A dimension/separation
    theorem is additionally required to obtain a proof-size lower bound.
    """
    source = replay_affine_dag(n, clauses, certificate,
                              max_assignments=max_assignments,
                              max_semantic_work=max_semantic_work)
    raw = source['raw']
    if (type(rank_limit) is not int or rank_limit < 1
            or rank_limit < max(map(len, raw), default=0)):
        raise ValueError('rank limit must include every raw input width')
    f = _poly(n, mask)
    if len(f) > max_monomials:
        raise ValueError('mask exceeds ordinary-PC output monomial cap')
    info = [clause_indicator(n, clause) for clause in source['clauses']]
    high = [item['rank'] is not None and item['rank'] > rank_limit for item in info]
    for j, assignment in enumerate(source['assignments']):
        if _eval(f, assignment):
            for i, discarded in enumerate(high):
                if discarded and not (source['truth'][i] >> j & 1):
                    raise ValueError('mask does not vanish on a high-rank falsity flat')
    builder = _Builder(n, raw, (), max_nodes, max_monomials)
    roots = {}
    cases = {'input': 0, 'zero_high_parents': 0, 'one_high_parent': 0,
             'two_high_parents': 0, 'discarded': 0, 'tautology': 0}
    for ix, node in enumerate(certificate['nodes']):
        if high[ix]:
            cases['discarded'] += 1
            continue
        q = info[ix]['polynomial']
        target = poly_mul(f, q)
        if info[ix]['rank'] is None:
            cases['tautology'] += 1
        if node['op'] == 'input':
            candidate = _times(builder, builder.raw_clause(node['input']), f)
            cases['input'] += 1
        else:
            parents = node['parents']
            low = [p for p in parents if not high[p]]
            num_high = len(parents) - len(low)
            cases[('zero_high_parents', 'one_high_parent', 'two_high_parents')[num_high]] += 1
            if not low:
                candidate = builder.zero()
            elif len(low) == 1:
                candidate = _times(builder, roots[low[0]], q)
            else:
                a, b = low
                first = _times(builder, roots[a], q)
                second = _times(builder, roots[b], poly_mul(q, ONE ^ info[a]['polynomial']))
                candidate = builder.add(first, second)
        error = target ^ builder.polynomials[candidate]
        correction = _boolean_zero(builder, error)
        roots[ix] = builder.add(candidate, correction)
        if builder.polynomials[roots[ix]] != target:
            raise AssertionError('masked line identity failed')
    bound = _degree(f) + 3 * rank_limit
    output = builder.export(roots[len(info) - 1])
    replay = replay_parity_pc(n, raw, output, max_degree=bound,
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if replay['root'] != f:
        raise AssertionError('masked DAG replay does not derive its mask')
    return dict(status='COMPLETE', certificate=output,
                profile=dict(source['profile'], rank_limit=rank_limit,
                             mask_degree=_degree(f), guaranteed_degree=bound,
                             cases=cases, **replay['profile']))
