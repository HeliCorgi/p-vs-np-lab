"""Finite exact ordinary F2 PC spaces, with replay and closure certificates.

The monomial universe is the ordinary polynomial space of total degree at most
``bound``.  Repeated variables are not reduced for free.  This is a deliberately
small-instance tool: the universe has binomial(n + bound, bound) coordinates.

Static axiom multiples are only a comparison.  The PC finder repeatedly
multiplies *derived* low-degree rows after cancellation.  Its certificate is
checked in both directions: every basis row has an ordinary-PC derivation, and
the resulting space contains every eligible axiom and is closed under every
permitted multiplication.  Thus a completed run determines the whole C_bound,
not just a collection of successful derivations.
"""
from itertools import combinations_with_replacement

from .parity_pc import KIND as TRACE_KIND, replay_parity_pc
from .parity_query import _input


KIND = 'ordinary-pc-f2-subspace-v1'
STATIC_KIND = 'ordinary-static-f2-moment-v1'
MAX_MONOMIALS = 20000
MAX_NODES = 200000
MAX_TRACE_TERMS = 2000000
MAX_WORK = 5000000


class PCSubspaceLimit(ValueError):
    pass


def _parameters(bound, target_degree, max_monomials, max_nodes,
                max_trace_terms, max_work):
    if type(bound) is not int or bound < 0:
        raise ValueError('invalid ordinary-PC degree bound')
    if target_degree is None:
        target_degree = bound
    if type(target_degree) is not int or not 0 <= target_degree <= bound:
        raise ValueError('invalid separated-space degree')
    if any(type(cap) is not int or cap < 0 for cap in
           (max_monomials, max_nodes, max_trace_terms, max_work)):
        raise ValueError('invalid ordinary-PC subspace budget')
    return target_degree


def _monomials(n, bound, cap):
    # Stop before constructing enormous integers or iterating through a huge
    # degree.  The binomial partial products are positive and nondecreasing.
    count = 1
    for j in range(1, min(n, bound) + 1):
        count = count * (n + bound - j + 1) // j
        if count > cap:
            raise PCSubspaceLimit('ordinary-PC monomial-universe cap')
    if count > cap:
        raise PCSubspaceLimit('ordinary-PC monomial-universe cap')
    if not n or not bound:
        return [()]
    return [m for degree in range(bound + 1)
            for m in combinations_with_replacement(range(1, n + 1), degree)]


def _clause_polynomial(clause):
    terms = {()}
    for literal in clause:
        product = {tuple(sorted((*m, abs(literal)))) for m in terms}
        terms = terms ^ product if literal > 0 else product
    return frozenset(terms)


def _axioms(n, raw, bound):
    for index, clause in enumerate(raw):
        # A product of len(clause) nonzero affine factors in an ordinary
        # polynomial ring has precisely this degree, including repetitions.
        if len(clause) <= bound:
            yield dict(op='input', clause=index), _clause_polynomial(clause)
    if bound >= 2:
        for variable in range(1, n + 1):
            yield dict(op='boolean', variable=variable), frozenset(
                {(variable,), (variable, variable)})


def _bits(terms, columns):
    out = 0
    for monomial in terms:
        out ^= 1 << columns[monomial]
    return out


def _insert_bits(basis, row):
    while row:
        pivot = row.bit_length() - 1
        if pivot not in basis:
            basis[pivot] = row
            return pivot
        row ^= basis[pivot]
    return None


def _reduce_bits(basis, row):
    while row:
        pivot = row.bit_length() - 1
        if pivot not in basis:
            return row
        row ^= basis[pivot]
    return 0


class _Finder:
    def __init__(self, n, raw, bound, monomials, max_nodes,
                 max_trace_terms, max_work):
        self.n, self.raw, self.bound = n, raw, bound
        self.monomials = monomials
        self.columns = {m: i for i, m in enumerate(monomials)}
        self.max_nodes, self.max_trace_terms = max_nodes, max_trace_terms
        self.max_work = max_work
        self.work = self.trace_terms = self.actual_degree = 0
        self.nodes, self.rows, self.memo = [], [], {}
        self.basis, self.basis_nodes, self.pending = {}, {}, []
        self.product_rows = self.axiom_rows = 0

    def spend(self, amount=1):
        self.work += amount
        if self.work > self.max_work:
            raise PCSubspaceLimit('ordinary-PC subspace work cap')

    def emit(self, node, row):
        if row in self.memo:
            return self.memo[row]
        if len(self.nodes) >= self.max_nodes:
            raise PCSubspaceLimit('ordinary-PC subspace trace-node cap')
        self.trace_terms += row.bit_count()
        if self.trace_terms > self.max_trace_terms:
            raise PCSubspaceLimit('ordinary-PC subspace trace-term cap')
        index = len(self.nodes)
        self.nodes.append(node)
        self.rows.append(row)
        self.memo[row] = index
        if row:
            self.actual_degree = max(self.actual_degree,
                                     len(self.monomials[row.bit_length() - 1]))
        return index

    def insert(self, row, node):
        while row:
            pivot = row.bit_length() - 1
            if pivot not in self.basis:
                self.basis[pivot] = row
                self.basis_nodes[pivot] = node
                if len(self.monomials[pivot]) < self.bound:
                    self.pending.append(pivot)
                return
            self.spend()
            row ^= self.basis[pivot]
            node = self.emit(dict(op='add', left=node,
                                  right=self.basis_nodes[pivot]), row)

    def product(self, row, monomial):
        result = 0
        while row:
            bit = row & -row
            source = self.monomials[bit.bit_length() - 1]
            target = tuple(sorted((*source, *monomial)))
            result ^= 1 << self.columns[target]
            row ^= bit
            self.spend()
        return result

    def find(self):
        self.emit(dict(op='zero'), 0)
        for clause in self.raw:
            if (len(clause) <= self.bound
                    and (1 << sum(literal > 0 for literal in clause)) > self.max_trace_terms):
                # Match the independent trace replayer's explicit raw-factor
                # expansion cap even when cancellations make the result small.
                raise PCSubspaceLimit('ordinary-PC raw replay expansion cap')
        axioms = []
        for operation, terms in _axioms(self.n, self.raw, self.bound):
            self.spend(len(terms) + 1)
            row = _bits(terms, self.columns)
            axioms.append(row)
            node = self.emit(operation, row)
            self.insert(row, node)
            self.axiom_rows += 1
        cursor = 0
        while cursor < len(self.pending):
            pivot = self.pending[cursor]
            cursor += 1
            row, node = self.basis[pivot], self.basis_nodes[pivot]
            for variable in range(1, self.n + 1):
                self.product_rows += 1
                multiplied = self.product(row, (variable,))
                child = self.emit(dict(op='multiply', parent=node,
                                       variable=variable), multiplied)
                self.insert(multiplied, child)
        # This finite span is deliberately not used to replace the PC closure.
        static = {}
        for row in axioms:
            degree = len(self.monomials[row.bit_length() - 1])
            for monomial in self.monomials:
                if len(monomial) > self.bound - degree:
                    break
                self.spend()
                multiple = self.product(row, monomial)
                while multiple:
                    pivot = multiple.bit_length() - 1
                    if pivot not in static:
                        static[pivot] = multiple
                        break
                    self.spend()
                    multiple ^= static[pivot]
        return static


def pc_subspace(n, clauses, *, bound, target_degree=None,
                max_monomials=MAX_MONOMIALS, max_nodes=MAX_NODES,
                max_trace_terms=MAX_TRACE_TERMS, max_work=MAX_WORK):
    """Return the exact bounded-degree space, or UNKNOWN on budget exhaustion.

    COMPLETE means the *finite PC space* was completely determined.  A false
    ``refutes`` value is neither SAT nor a statement about higher degrees.
    ``separated_monomials`` span an explicit maximum-dimensional complement
    to C_bound inside the ordinary degree-at-most-target_degree space.
    """
    raw = _input(n, clauses)
    target_degree = _parameters(bound, target_degree, max_monomials, max_nodes,
                                max_trace_terms, max_work)
    finder = None
    try:
        monomials = _monomials(n, bound, max_monomials)
        finder = _Finder(n, raw, bound, monomials, max_nodes,
                         max_trace_terms, max_work)
        static = finder.find()
        selected = [i for i, m in enumerate(monomials) if len(m) <= target_degree]
        separated = [list(monomials[i]) for i in selected if i not in finder.basis]
        static_refutes = _reduce_bits(static, 1) == 0
        static_separator = None
        if not static_refutes:
            dual = 1
            for pivot in sorted(static):
                if (static[pivot] & dual).bit_count() % 2:
                    dual |= 1 << pivot
            static_separator = dict(
                kind=STATIC_KIND, field=2, variables=n, bound=bound,
                one_monomials=[list(m) for i, m in enumerate(monomials)
                               if dual >> i & 1])
        profile = dict(
            variables=n, bound=bound, target_degree=target_degree,
            ambient_dimension=len(monomials), basis_rank=len(finder.basis),
            low_degree_dimension=len(selected),
            low_degree_consequence_rank=sum(i in finder.basis for i in selected),
            separated_dimension=len(separated),
            static_basis_rank=len(static),
            static_low_degree_rank=sum(i in static for i in selected),
            static_separated_dimension=sum(i not in static for i in selected),
            static_refutes=static_refutes,
            refutes=_reduce_bits(finder.basis, 1) == 0,
            eligible_axioms=finder.axiom_rows,
            omitted_clause_axioms=sum(len(c) > bound for c in raw),
            multiplied_derived_rows=finder.product_rows,
            trace_nodes=len(finder.nodes), trace_terms=finder.trace_terms,
            actual_trace_degree=finder.actual_degree, work=finder.work,
            budget_limited=False)
        certificate = dict(
            kind=KIND, field=2, variables=n, bound=bound,
            target_degree=target_degree,
            trace=dict(kind=TRACE_KIND, field=2, variables=n,
                       degree=finder.actual_degree, nodes=finder.nodes,
                       root=len(finder.nodes) - 1),
            basis=[finder.basis_nodes[p] for p in sorted(finder.basis)],
            separated_monomials=separated)
        return dict(status='COMPLETE', profile=profile, certificate=certificate,
                    static_separator=static_separator)
    except PCSubspaceLimit as exc:
        return dict(status='UNKNOWN', reason=str(exc), certificate=None,
                    profile=dict(budget_limited=True,
                                 work=0 if finder is None else finder.work,
                                 trace_nodes=0 if finder is None else len(finder.nodes)))


def _sparse_insert(basis, polynomial, column):
    row = set(polynomial)
    while row:
        pivot = max(row, key=column.__getitem__)
        if pivot not in basis:
            basis[pivot] = frozenset(row)
            return
        row.symmetric_difference_update(basis[pivot])


def _sparse_member(basis, polynomial, column):
    row = set(polynomial)
    while row:
        pivot = max(row, key=column.__getitem__)
        if pivot not in basis:
            return False
        row.symmetric_difference_update(basis[pivot])
    return True


def replay_pc_subspace(n, clauses, certificate, *, bound=None, target_degree=None,
                       generators=None,
                       max_monomials=MAX_MONOMIALS, max_nodes=MAX_NODES,
                       max_trace_terms=MAX_TRACE_TERMS, max_work=MAX_WORK):
    """Check derivability *and* completeness independently with sparse rows.

    The checker does not run the finder, trust its dimensions, or use bitset
    elimination.  A sparse echelon basis exposes the low-degree part, so
    closure of its rows under multiplication suffices by linearity.
    """
    raw = _input(n, clauses)
    if (type(certificate) is not dict or set(certificate) != {
            'kind', 'field', 'variables', 'bound', 'target_degree', 'trace',
            'basis', 'separated_monomials'} or certificate['kind'] != KIND
            or type(certificate['field']) is not int or certificate['field'] != 2
            or type(certificate['variables']) is not int or certificate['variables'] != n):
        raise ValueError('invalid PC subspace certificate')
    claimed_bound = certificate['bound']
    claimed_target = certificate['target_degree']
    _parameters(claimed_bound, claimed_target, max_monomials, max_nodes,
                max_trace_terms, max_work)
    if ((bound is not None and (type(bound) is not int or bound != claimed_bound))
            or (target_degree is not None and
                (type(target_degree) is not int or target_degree != claimed_target))):
        raise ValueError('PC subspace degree binding mismatch')
    monomials = _monomials(n, claimed_bound, max_monomials)
    columns = {m: i for i, m in enumerate(monomials)}
    replay = replay_parity_pc(n, raw, certificate['trace'], max_degree=claimed_bound,
                             max_nodes=max_nodes, max_monomials=max_trace_terms)
    polynomials = replay['polynomials']
    nodes = certificate['basis']
    if (type(nodes) is not list or any(type(i) is not int or not 0 <= i < len(polynomials)
                                     for i in nodes) or len(nodes) != len(set(nodes))):
        raise ValueError('invalid PC subspace basis references')
    basis = {}
    work = 0
    for i in nodes:
        work += len(polynomials[i]) + 1
        _sparse_insert(basis, polynomials[i], columns)
    if len(basis) != len(nodes):
        raise ValueError('dependent or zero PC subspace basis row')
    eligible = 0
    for _, polynomial in _axioms(n, raw, claimed_bound):
        work += len(polynomial) + 1
        if work > max_work:
            raise PCSubspaceLimit('ordinary-PC closure-check work cap')
        if not _sparse_member(basis, polynomial, columns):
            raise ValueError('PC subspace omits an eligible axiom')
        eligible += 1
    multiplication_checks = 0
    for pivot, polynomial in basis.items():
        if len(pivot) >= claimed_bound:
            continue
        for variable in range(1, n + 1):
            multiplication_checks += 1
            work += len(polynomial) + 1
            if work > max_work:
                raise PCSubspaceLimit('ordinary-PC closure-check work cap')
            product = {tuple(sorted((*m, variable))) for m in polynomial}
            if not _sparse_member(basis, product, columns):
                raise ValueError('PC subspace not closed under permitted multiplication')
    # Echelon leading monomials are ordered first by total degree.  Therefore
    # rows headed in degree <= k span exactly the intersection with P_k.
    selected = [m for m in monomials if len(m) <= claimed_target]
    complement = [list(m) for m in selected if m not in basis]
    if certificate['separated_monomials'] != complement:
        raise ValueError('incorrect separated monomial complement')
    if any(type(m) is not list or any(type(v) is not int for v in m)
           for m in certificate['separated_monomials']):
        raise ValueError('invalid separated monomial')
    result = dict(ambient_dimension=len(monomials), basis_rank=len(basis),
                  low_degree_dimension=len(selected),
                  low_degree_consequence_rank=sum(m in basis for m in selected),
                  separated_dimension=len(complement),
                  refutes=_sparse_member(basis, {()}, columns),
                  eligible_axioms=eligible, multiplication_checks=multiplication_checks,
                  separated_monomials=complement,
                  proof_degree=replay['profile']['proof_degree'])
    if generators is not None:
        # A generator is a list of ordinary monomials, each a sorted list of
        # variable indices.  Repeated equal monomials cancel in F2.
        candidate = {}
        count = 0
        if isinstance(generators, (str, bytes)):
            raise ValueError('invalid candidate polynomial space')
        for polynomial in generators:
            if not isinstance(polynomial, (list, tuple)):
                raise ValueError('invalid candidate polynomial')
            terms = set()
            for monomial in polynomial:
                if (not isinstance(monomial, (list, tuple))
                        or len(monomial) > claimed_target
                        or any(type(v) is not int or not 1 <= v <= n for v in monomial)
                        or list(monomial) != sorted(monomial)):
                    raise ValueError('invalid candidate monomial')
                value = tuple(monomial)
                if value in terms:
                    terms.remove(value)
                else:
                    terms.add(value)
            work += len(terms) + 1
            if work > max_work:
                raise PCSubspaceLimit('ordinary-PC candidate-space work cap')
            _sparse_insert(candidate, terms, columns)
            count += 1
        union = dict(basis)
        for polynomial in candidate.values():
            _sparse_insert(union, polynomial, columns)
        quotient_rank = len(union) - len(basis)
        intersection_dimension = len(candidate) - quotient_rank
        result['candidate'] = dict(generator_count=count, dimension=len(candidate),
                                   quotient_rank=quotient_rank,
                                   intersection_dimension=intersection_dimension,
                                   separated=intersection_dimension == 0)
    return result


def check_pc_subspace(n, clauses, certificate, **kwargs):
    try:
        replay_pc_subspace(n, clauses, certificate, **kwargs)
        return True
    except (ValueError, TypeError, IndexError, KeyError, AttributeError):
        return False


def check_static_moment(n, clauses, witness, *, bound=None,
                        max_monomials=MAX_MONOMIALS, max_work=MAX_WORK):
    """Check L(1)=1 and L(m*f)=0 for every eligible original axiom multiple.

    This witnesses failure of static Nullstellensatz at the indicated degree,
    and deliberately makes no claim about the stronger dynamic PC space.
    """
    try:
        raw = _input(n, clauses)
        if (type(witness) is not dict or set(witness) != {
                'kind', 'field', 'variables', 'bound', 'one_monomials'}
                or witness['kind'] != STATIC_KIND
                or type(witness['field']) is not int or witness['field'] != 2
                or type(witness['variables']) is not int or witness['variables'] != n):
            return False
        degree = witness['bound']
        _parameters(degree, degree, max_monomials, 0, 0, max_work)
        if bound is not None and (type(bound) is not int or degree != bound):
            return False
        monomials = _monomials(n, degree, max_monomials)
        universe = set(monomials)
        listed = witness['one_monomials']
        if type(listed) is not list:
            return False
        ones = set()
        for monomial in listed:
            if (type(monomial) is not list or any(type(v) is not int for v in monomial)
                    or tuple(monomial) not in universe or tuple(monomial) in ones):
                return False
            ones.add(tuple(monomial))
        if () not in ones:
            return False
        work = 0
        for _, polynomial in _axioms(n, raw, degree):
            axiom_degree = max(map(len, polynomial), default=0)
            for monomial in monomials:
                if len(monomial) + axiom_degree > degree:
                    break
                work += len(polynomial) + 1
                if work > max_work:
                    return False
                if sum(tuple(sorted((*term, *monomial))) in ones
                       for term in polynomial) % 2:
                    return False
        return True
    except (ValueError, TypeError, IndexError, KeyError, AttributeError):
        return False
