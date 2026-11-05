"""Explicit ordinary F2 polynomial-calculus discharge of parity assumptions.

Unlike polynomial_proof.py, monomials here retain repeated variables.  Boolean
identities are actual axiom lines x*x + x, never implicit reductions.  The
converter is a finite audit of a degree simulation, not a polynomial-size
proof generator: repeated discharge may greatly expand its sparse traces.
"""
from collections import Counter
from itertools import product

from .parity_query import _input, check_parity_query


KIND = 'ordinary-pc-f2-path-v1'
MAX_NODES = 200000
MAX_MONOMIALS = 2000000
ONE = frozenset({()})
ZERO = frozenset()


class PCTraceLimit(ValueError):
    pass


def _degree(polynomial):
    return max((len(monomial) for monomial in polynomial), default=0)


def _context(n, assumptions):
    if isinstance(assumptions, (str, bytes)):
        raise ValueError('invalid assumption list')
    out = []
    for equation in assumptions:
        if not isinstance(equation, (tuple, list)) or len(equation) != 2:
            raise ValueError('invalid affine assumption')
        scope, rhs = equation
        if (not isinstance(scope, (tuple, list))
                or any(type(v) is not int or not 1 <= v <= n for v in scope)
                or list(scope) != sorted(set(scope))
                or type(rhs) is not int or rhs not in (0, 1)):
            raise ValueError('invalid affine assumption')
        out.append((tuple(scope), rhs))
    return tuple(out)


def _affine(scope, constant):
    return frozenset((v,) for v in scope) ^ (ONE if constant else ZERO)


def _limits(max_degree, max_nodes, max_monomials):
    if max_degree is not None and (type(max_degree) is not int or max_degree < 0):
        raise ValueError('invalid degree cap')
    if any(type(cap) is not int or cap < 0 for cap in (max_nodes, max_monomials)):
        raise ValueError('invalid trace cap')


def replay_parity_pc(n, clauses, certificate, *, assumptions=(), max_degree=None,
                     max_nodes=MAX_NODES, max_monomials=MAX_MONOMIALS):
    """Independent ordinary-polynomial replay; the root may be any polynomial.

    The caller supplies all permitted affine assumptions.  An assumption
    stored only in an untrusted certificate is not an axiom.  Use
    check_parity_pc for a refutation, where the final polynomial must be 1.
    """
    raw = _input(n, clauses)
    context = _context(n, assumptions)
    _limits(max_degree, max_nodes, max_monomials)
    if (type(certificate) is not dict
            or set(certificate) != {'kind', 'field', 'variables', 'degree', 'nodes', 'root'}
            or certificate['kind'] != KIND or type(certificate['field']) is not int
            or certificate['field'] != 2 or type(certificate['variables']) is not int
            or certificate['variables'] != n or type(certificate['degree']) is not int
            or certificate['degree'] < 0 or type(certificate['nodes']) is not list
            or not certificate['nodes'] or type(certificate['root']) is not int
            or certificate['root'] != len(certificate['nodes']) - 1):
        raise ValueError('invalid ordinary-PC certificate')
    nodes = certificate['nodes']
    if len(nodes) > max_nodes:
        raise PCTraceLimit('ordinary-PC node cap')
    polynomials = []
    volume = degree = peak = 0
    operations = Counter()

    def parent(index, before):
        if type(index) is not int or not 0 <= index < before:
            raise ValueError('invalid ordinary-PC parent')
        return polynomials[index]

    for ix, node in enumerate(nodes):
        if type(node) is not dict:
            raise ValueError('invalid ordinary-PC node')
        tag = node.get('op')
        counts = Counter()
        if tag == 'zero' and set(node) == {'op'}:
            pass
        elif tag == 'input' and set(node) == {'op', 'clause'}:
            clause = node['clause']
            if type(clause) is not int or not 0 <= clause < len(raw):
                raise ValueError('invalid original clause')
            positive = [v for v in raw[clause] if v > 0]
            negative = [-v for v in raw[clause] if v < 0]
            if (1 << len(positive)) > max_monomials:
                raise PCTraceLimit('ordinary-PC raw expansion cap')
            # Repeated variables are deliberately retained, including squares.
            for choice in product((0, 1), repeat=len(positive)):
                counts[tuple(sorted(negative + [v for v, bit in zip(positive, choice) if bit]))] += 1
        elif tag == 'boolean' and set(node) == {'op', 'variable'}:
            v = node['variable']
            if type(v) is not int or not 1 <= v <= n:
                raise ValueError('invalid Boolean axiom variable')
            counts[(v, v)] += 1
            counts[(v,)] += 1
        elif tag == 'assumption' and set(node) == {'op', 'index'}:
            i = node['index']
            if type(i) is not int or not 0 <= i < len(context):
                raise ValueError('unavailable affine assumption')
            scope, rhs = context[i]
            counts.update((v,) for v in scope)
            if rhs:
                counts[()] += 1
        elif tag == 'add' and set(node) == {'op', 'left', 'right'}:
            counts.update(parent(node['left'], ix))
            counts.update(parent(node['right'], ix))
        elif tag == 'multiply' and set(node) == {'op', 'parent', 'variable'}:
            v = node['variable']
            if type(v) is not int or not 1 <= v <= n:
                raise ValueError('invalid multiplication variable')
            for monomial in parent(node['parent'], ix):
                counts[tuple(sorted((*monomial, v)))] += 1
        else:
            raise ValueError('invalid ordinary-PC operation')
        polynomial = frozenset(m for m, count in counts.items() if count % 2)
        polynomials.append(polynomial)
        degree = max(degree, _degree(polynomial))
        volume += len(polynomial)
        peak = max(peak, len(polynomial))
        if max_degree is not None and degree > max_degree:
            raise PCTraceLimit('ordinary-PC degree cap')
        if volume > max_monomials:
            raise PCTraceLimit('ordinary-PC monomial cap')
        operations[tag] += 1
    if certificate['degree'] != degree:
        raise ValueError('incorrect ordinary-PC degree declaration')
    return dict(polynomials=tuple(polynomials), root=polynomials[-1],
                profile=dict(proof_nodes=len(nodes), proof_degree=degree,
                             proof_monomial_occurrences=volume,
                             max_polynomial_monomials=peak,
                             operations=dict(sorted(operations.items()))))


def check_parity_pc(n, clauses, certificate, *, assumptions=(), max_degree=None,
                    max_nodes=MAX_NODES, max_monomials=MAX_MONOMIALS):
    try:
        result = replay_parity_pc(n, clauses, certificate, assumptions=assumptions,
                                 max_degree=max_degree, max_nodes=max_nodes,
                                 max_monomials=max_monomials)
        return result['root'] == ONE
    except (ValueError, TypeError, IndexError, KeyError, AttributeError):
        return False


class _Builder:
    def __init__(self, n, raw, context, max_nodes, max_monomials):
        self.n, self.raw, self.context = n, raw, context
        self.max_nodes, self.max_monomials = max_nodes, max_monomials
        self.nodes, self.polynomials, self.memo = [], [], {}
        self.volume = 0

    def emit(self, key, node, polynomial):
        if key in self.memo:
            return self.memo[key]
        if len(self.nodes) >= self.max_nodes:
            raise PCTraceLimit('ordinary-PC construction node cap')
        self.volume += len(polynomial)
        if self.volume > self.max_monomials:
            raise PCTraceLimit('ordinary-PC construction monomial cap')
        ix = len(self.nodes)
        self.nodes.append(node)
        self.polynomials.append(polynomial)
        self.memo[key] = ix
        return ix

    def zero(self):
        return self.emit(('zero',), dict(op='zero'), ZERO)

    def raw_clause(self, ix):
        key = ('input', ix)
        if key in self.memo:
            return self.memo[key]
        value = ONE
        for literal in self.raw[ix]:
            times = frozenset(tuple(sorted((*m, abs(literal)))) for m in value)
            value = times ^ value if literal > 0 else times
            if len(value) > self.max_monomials:
                raise PCTraceLimit('ordinary-PC construction expansion cap')
        return self.emit(key, dict(op='input', clause=ix), value)

    def boolean(self, v):
        return self.emit(('boolean', v), dict(op='boolean', variable=v),
                         frozenset({(v,), (v, v)}))

    def assumption(self, ix):
        return self.emit(('assumption', ix), dict(op='assumption', index=ix),
                         _affine(*self.context[ix]))

    def add(self, left, right):
        left, right = sorted((left, right))
        return self.emit(('add', left, right), dict(op='add', left=left, right=right),
                         self.polynomials[left] ^ self.polynomials[right])

    def multiply(self, parent, variable):
        polynomial = frozenset(tuple(sorted((*m, variable))) for m in self.polynomials[parent])
        return self.emit(('multiply', parent, variable),
                         dict(op='multiply', parent=parent, variable=variable), polynomial)

    def times_affine(self, parent, scope, constant):
        terms = ([parent] if constant else []) + [self.multiply(parent, v) for v in scope]
        return self.sum(terms)

    def sum(self, terms):
        terms = list(terms)
        if not terms:
            return self.zero()
        result = terms[0]
        for term in terms[1:]:
            result = self.add(result, term)
        return result

    def export(self, root):
        needed = set()
        todo = [root]
        while todo:
            ix = todo.pop()
            if ix in needed:
                continue
            needed.add(ix)
            node = self.nodes[ix]
            if node['op'] == 'add':
                todo.extend((node['left'], node['right']))
            elif node['op'] == 'multiply':
                todo.append(node['parent'])
        order = sorted(needed)
        rename = {old: new for new, old in enumerate(order)}
        nodes = []
        for old in order:
            node = self.nodes[old].copy()
            if node['op'] == 'add':
                node['left'], node['right'] = rename[node['left']], rename[node['right']]
            elif node['op'] == 'multiply':
                node['parent'] = rename[node['parent']]
            nodes.append(node)
        return dict(kind=KIND, field=2, variables=self.n,
                    degree=max(_degree(self.polynomials[i]) for i in order),
                    nodes=nodes, root=rename[root])


def discharge_parity_pc(n, clauses, certificate, *, assumptions, index,
                        max_nodes=MAX_NODES, max_monomials=MAX_MONOMIALS):
    """From Gamma,a |- 1 derive Gamma |- 1+a in degree max(D+1,2).

    The returned root is 1+a, usually not a refutation by itself.  No axiom a
    survives; every use of a(1+a) is replaced by a sum of Boolean axioms.
    """
    raw = _input(n, clauses)
    context = _context(n, assumptions)
    if type(index) is not int or not 0 <= index < len(context):
        raise ValueError('invalid discharged assumption')
    source = replay_parity_pc(n, raw, certificate, assumptions=context,
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if source['root'] != ONE:
        raise ValueError('source is not a refutation')
    scope, rhs = context[index]
    remaining = context[:index] + context[index+1:]
    builder = _Builder(n, raw, remaining, max_nodes, max_monomials)
    translated = []
    for node in certificate['nodes']:
        tag = node['op']
        if tag == 'assumption' and node['index'] == index:
            # In the ordinary ring, a(1+a) = a+a^2 = sum_v (v+v^2).
            root = builder.sum(builder.boolean(v) for v in scope)
        elif tag in ('input', 'boolean', 'assumption', 'zero'):
            if tag == 'input': base = builder.raw_clause(node['clause'])
            elif tag == 'boolean': base = builder.boolean(node['variable'])
            elif tag == 'zero': base = builder.zero()
            else:
                old = node['index']
                base = builder.assumption(old - int(old > index))
            root = builder.times_affine(base, scope, rhs ^ 1)
        elif tag == 'add':
            root = builder.add(translated[node['left']], translated[node['right']])
        else:
            root = builder.multiply(translated[node['parent']], node['variable'])
        translated.append(root)
    output = builder.export(translated[-1])
    replay = replay_parity_pc(n, raw, output, assumptions=remaining,
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if (replay['root'] != _affine(scope, rhs ^ 1)
            or output['degree'] > max(certificate['degree'] + 1, 2)):
        raise AssertionError('ordinary-PC discharge identity or degree failed')
    return output


def _import_trace(builder, certificate, replacements=None):
    replacements = {} if replacements is None else replacements
    ids = []
    for node in certificate['nodes']:
        tag = node['op']
        if tag == 'zero': root = builder.zero()
        elif tag == 'input': root = builder.raw_clause(node['clause'])
        elif tag == 'boolean': root = builder.boolean(node['variable'])
        elif tag == 'assumption':
            root = (replacements[node['index']] if node['index'] in replacements
                    else builder.assumption(node['index']))
        elif tag == 'add': root = builder.add(ids[node['left']], ids[node['right']])
        else: root = builder.multiply(ids[node['parent']], node['variable'])
        ids.append(root)
    return ids[-1]


def glue_parity_pc(n, clauses, query, zero, one, *, assumptions=(), zero_rank=None,
                   one_rank=None, max_nodes=MAX_NODES, max_monomials=MAX_MONOMIALS):
    """Eliminate one query, discharging the child with lower certified rank.

    With ranks a,b >= 2 bounding the child degrees, the parent rank is
    max(a,b) when a != b and a+1 otherwise.  Ranks do not affect soundness:
    all final arithmetic is independently replayed against the old context.
    """
    raw = _input(n, clauses)
    context = _context(n, assumptions)
    query = _context(n, [(query, 0)])[0][0]
    proofs = (zero, one)
    profiles = []
    for bit, proof in enumerate(proofs):
        result = replay_parity_pc(n, raw, proof, assumptions=context + ((query, bit),),
                                 max_nodes=max_nodes, max_monomials=max_monomials)
        if result['root'] != ONE:
            raise ValueError('child is not a refutation in its actual context')
        profiles.append(result['profile'])
    ranks = [zero_rank, one_rank]
    for bit in (0, 1):
        if ranks[bit] is None:
            ranks[bit] = max(2, proofs[bit]['degree'])
        if type(ranks[bit]) is not int or ranks[bit] < max(2, proofs[bit]['degree']):
            raise ValueError('child rank does not bound its ordinary degree')
    smaller = int(ranks[1] < ranks[0])
    larger = smaller ^ 1
    rank = max(ranks) + int(ranks[0] == ranks[1])
    discharged = discharge_parity_pc(n, raw, proofs[smaller],
                                    assumptions=context + ((query, smaller),), index=len(context),
                                    max_nodes=max_nodes, max_monomials=max_monomials)
    builder = _Builder(n, raw, context, max_nodes, max_monomials)
    opposite = _import_trace(builder, discharged)
    root = _import_trace(builder, proofs[larger], {len(context): opposite})
    output = builder.export(root)
    result = replay_parity_pc(n, raw, output, assumptions=context,
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if result['root'] != ONE or output['degree'] > rank:
        raise AssertionError('ordinary-PC branch composition failed')
    return dict(certificate=output, rank=rank, discharged_branch=smaller,
                child_ranks=ranks, child_degrees=[p['proof_degree'] for p in profiles],
                profile=result['profile'])


def _leaf_proof(n, raw, context, node, max_nodes, max_monomials):
    builder = _Builder(n, raw, context, max_nodes, max_monomials)
    variables = sorted({v for scope, _ in context for v in scope}
                       | {abs(lit) for clause in raw for lit in clause})
    positions = {v: j for j, v in enumerate(variables)}
    basis = {}

    def combination(trace):
        return builder.sum(builder.assumption(i) for i in range(len(context)) if trace >> i & 1)

    for i, (scope, rhs) in enumerate(context):
        row = sum(1 << positions[v] for v in scope)
        trace = 1 << i
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row, rhs, trace
                break
            old, bit, why = basis[pivot]
            row ^= old
            rhs ^= bit
            trace ^= why
        if not row and rhs:
            return builder.export(combination(trace))
    if 'clause' not in node:
        raise AssertionError('claimed inconsistent leaf has a consistent path')
    clause = raw[node['clause']]
    terms = []
    for offset, literal in enumerate(clause):
        variable = abs(literal)
        row, rhs, trace = 1 << positions[variable], 0, 0
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                raise AssertionError('raw leaf does not force a literal')
            old, bit, why = basis[pivot]
            row ^= old
            rhs ^= bit
            trace ^= why
        if rhs != int(literal < 0):
            raise AssertionError('raw leaf forces the wrong literal value')
        term = combination(trace)
        for earlier in clause[:offset]:
            times = builder.multiply(term, abs(earlier))
            term = builder.add(term, times) if earlier > 0 else times
        terms.append(term)
    # sum_i (f_i+1) prod_{j<i} f_j = 1 + prod_i f_i, in the ordinary ring.
    root = builder.add(builder.raw_clause(node['clause']), builder.sum(terms))
    output = builder.export(root)
    result = replay_parity_pc(n, raw, output, assumptions=context,
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if result['root'] != ONE:
        raise AssertionError('ordinary raw-leaf translation failed')
    return output


def parity_tree_to_pc(n, clauses, tree, *, max_nodes=MAX_NODES,
                      max_monomials=MAX_MONOMIALS):
    """Finite conversion of a checked raw-leaf parity tree to ordinary PC.

    Leaf weights are 2^max(2,d_leaf).  The certified root rank r obeys
    2^r <= their sum, and actual ordinary degree <= r.  A size cap returns
    UNKNOWN; this is not a polynomial-size simulation claim.
    """
    raw = _input(n, clauses)
    _limits(None, max_nodes, max_monomials)
    if not check_parity_query(n, raw, tree):
        raise ValueError('invalid raw-leaf parity tree')
    contexts = [None] * len(tree['nodes'])
    contexts[0] = ()
    for ix, node in enumerate(tree['nodes']):
        if 'query' in node:
            for bit, side in enumerate(('zero', 'one')):
                contexts[node[side]] = contexts[ix] + ((tuple(node['query']), bit),)
    results = {}
    histogram = Counter()
    glue_records = []
    try:
        for ix in reversed(range(len(tree['nodes']))):
            node, context = tree['nodes'][ix], contexts[ix]
            if 'query' not in node:
                proof = _leaf_proof(n, raw, context, node, max_nodes, max_monomials)
                degree = proof['degree']
                rank = max(2, degree)
                histogram[degree] += 1
                results[ix] = dict(certificate=proof, rank=rank, mass=1 << rank,
                                   leaves=1, max_leaf_degree=rank, depth=0)
            else:
                left, right = (results.pop(node[side]) for side in ('zero', 'one'))
                combined = glue_parity_pc(n, raw, node['query'], left['certificate'], right['certificate'],
                                         assumptions=context, zero_rank=left['rank'], one_rank=right['rank'],
                                         max_nodes=max_nodes, max_monomials=max_monomials)
                mass = left['mass'] + right['mass']
                if (1 << combined['rank']) > mass:
                    raise AssertionError('weighted rank inequality failed')
                glue_records.append(dict(tree_node=ix, rank=combined['rank'],
                                         child_ranks=combined['child_ranks'],
                                         child_degrees=combined['child_degrees'],
                                         discharged_branch=combined['discharged_branch'],
                                         actual_degree=combined['certificate']['degree']))
                results[ix] = dict(certificate=combined['certificate'], rank=combined['rank'],
                                   mass=mass, leaves=left['leaves'] + right['leaves'],
                                   max_leaf_degree=max(left['max_leaf_degree'], right['max_leaf_degree']),
                                   depth=1 + max(left['depth'], right['depth']))
    except PCTraceLimit as exc:
        return dict(status='UNKNOWN', certificate=None,
                    stats=dict(budget_limited=True, reason=str(exc)))
    result = results[0]
    bound = result['max_leaf_degree'] + result['leaves'].bit_length() - 1
    if result['rank'] > bound:
        raise AssertionError('uniform leaf-count bound failed')
    replay = replay_parity_pc(n, raw, result['certificate'],
                             max_nodes=max_nodes, max_monomials=max_monomials)
    if replay['root'] != ONE:
        raise AssertionError('root is not an unconditional ordinary-PC refutation')
    stats = dict(replay['profile'], budget_limited=False, certified_rank=result['rank'],
                 weighted_leaf_mass=result['mass'], leaves=result['leaves'],
                 max_leaf_degree=result['max_leaf_degree'], leaf_count_degree_bound=bound,
                 query_tree_depth=result['depth'],
                 actual_leaf_degree_histogram={str(k): v for k, v in sorted(histogram.items())},
                 branch_glue=sorted(glue_records, key=lambda row: row['tree_node']))
    return dict(status='UNSAT', certificate=result['certificate'], stats=stats)
