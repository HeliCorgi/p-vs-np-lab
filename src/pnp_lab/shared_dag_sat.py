"""Exact Boolean cofactoring with structural sharing and bounded experiments.

This is an experimental SAT solver, not a polynomial-time algorithm. A resource
limit returns UNKNOWN. Node identities mean identical normalized syntax, not
Boolean equivalence. No distributive expansion or subset factor search occurs.
"""
from .circuit_extensions import Circuit, Gate


class BudgetExceeded(RuntimeError):
    """An explicit experimental budget was exhausted."""


def complement(edge):
    return 1 - edge if edge in (0, 1) else -edge


class SharedDAG:
    """Constants 0/1, positive node IDs, and negative complemented edges."""

    def __init__(self, *, max_nodes=200_000, max_work=5_000_000):
        for name, value in (("max_nodes", max_nodes), ("max_work", max_work)):
            if value is not None and (type(value) is not int or value < 0):
                raise ValueError(f"{name} must be a nonnegative integer or None")
        self.max_nodes, self.max_work = max_nodes, max_work
        self.nodes = {}
        self.unique = {}
        self.supports = {0: frozenset(), 1: frozenset()}
        self.work = 0
        self.cofactor_visits = 0

    def tick(self, amount=1):
        self.work += amount
        if self.max_work is not None and self.work > self.max_work:
            raise BudgetExceeded("simplification/cofactor work budget")

    def _intern(self, kind, payload):
        self.tick()
        key = (kind, payload)
        if key in self.unique:
            return self.unique[key]
        if self.max_nodes is not None and len(self.nodes) >= self.max_nodes:
            raise BudgetExceeded("interned node budget")
        edge = len(self.nodes) + 2
        support = (frozenset((payload,)) if kind == 'var' else
                   frozenset().union(*(self.supports[abs(e)] for e in payload)))
        self.nodes[edge] = key
        self.supports[edge] = support
        self.unique[key] = edge
        return edge

    def variable(self, label):
        if type(label) is not int or label < 1:
            raise ValueError("Variable labels must be positive integers")
        return self._intern('var', label)

    def conjunction(self, edges):
        pending = list(edges)
        factors = set()
        while pending:
            self.tick()
            edge = pending.pop()
            if edge == 0:
                return 0
            if edge == 1:
                continue
            if edge > 1 and self.nodes[edge][0] == 'and':
                pending.extend(self.nodes[edge][1])
                continue
            if complement(edge) in factors:
                return 0
            factors.add(edge)
        if not factors:
            return 1
        if len(factors) == 1:
            return next(iter(factors))
        return self._intern('and', tuple(sorted(factors)))

    def exclusive_or(self, edges):
        wrappers = []
        while True:
            result, wrapper, residuals = self._xor_step(edges)
            if wrapper is None:
                break
            wrappers.append(wrapper)
            edges = residuals
        for common, parity in reversed(wrappers):
            result = self.conjunction((*common, result))
            if parity:
                result = complement(result)
        return result

    def _xor_step(self, edges):
        # Explicit continuations above also avoid recursion during factoring.
        pending = list(edges)
        parity, terms = False, set()
        while pending:
            self.tick()
            edge = pending.pop()
            if edge in (0, 1):
                parity ^= bool(edge)
                continue
            if edge < 0:
                parity = not parity
                edge = -edge
            kind, payload = self.nodes[edge]
            if kind == 'xor':
                pending.extend(payload)
                continue
            if edge in terms:
                terms.remove(edge)
            else:
                terms.add(edge)
        ordered = tuple(sorted(terms))
        if not ordered:
            return int(parity), None, None
        if len(ordered) == 1:
            result = ordered[0]
        else:
            # Only the intersection across ALL terms; no search over subsets.
            factors = [set(self.nodes[e][1]) if self.nodes[e][0] == 'and'
                       else {e} for e in ordered]
            self.tick(sum(map(len, factors)))
            common = set.intersection(*factors)
            if common:
                residuals = [self.conjunction(sorted(fs - common)) for fs in factors]
                return None, (tuple(sorted(common)), parity), residuals
            else:
                result = self._intern('xor', ordered)
        return (complement(result) if parity else result), None, None

    def disjunction(self, edges):
        return complement(self.conjunction(complement(e) for e in edges))

    def cofactor(self, root, variable, value):
        """Substitute one variable, rebuilding reachable nodes in topological order."""
        reachable, pending = set(), [abs(root)]
        while pending:
            edge = pending.pop()
            if edge < 2 or edge in reachable or variable not in self.supports[edge]:
                continue
            self.tick()
            self.cofactor_visits += 1
            reachable.add(edge)
            kind, payload = self.nodes[edge]
            if kind != 'var':
                pending.extend(abs(e) for e in payload)
        mapped = {0: 0, 1: 1}

        def lookup(edge):
            result = mapped.get(abs(edge), abs(edge))
            return complement(result) if edge < 0 else result

        # Every node references strictly older nodes, including complemented ones.
        for edge in sorted(reachable):
            kind, payload = self.nodes[edge]
            if kind == 'var':
                mapped[edge] = int(value)
            else:
                operation = self.conjunction if kind == 'and' else self.exclusive_or
                mapped[edge] = operation(lookup(e) for e in payload)
        return lookup(root)

    def from_circuit(self, circuit):
        wires = [0] + [self.variable(i) for i in range(1, circuit.inputs + 1)]
        for gate in circuit.gates:
            args = [wires[w] for w in gate.inputs]
            if gate.kind == 'NOT':
                edge = complement(args[0])
            elif gate.kind == 'AND':
                edge = self.conjunction(args)
            else:
                edge = self.exclusive_or(args)
            wires.append(edge)
        return wires[circuit.output]


def _order(labels, order):
    result = tuple(sorted(labels)) if order is None else tuple(order)
    if (any(type(v) is not int for v in result) or len(result) != len(labels)
            or set(result) != set(labels)):
        raise ValueError("Order must contain every input variable exactly once")
    return result


def _solve(build, labels, order, max_states, max_nodes, max_work):
    order = _order(labels, order)
    if max_states is not None and (type(max_states) is not int or max_states < 0):
        raise ValueError("max_states must be a nonnegative integer or None")
    manager = SharedDAG(max_nodes=max_nodes, max_work=max_work)
    stats = dict(input_nodes=None, expanded_states=0, memo_hits=0, states_by_variable={})
    result = dict(status='UNKNOWN', assignment=None, reason=None, stats=stats)
    try:
        root = build(manager)
        stats['input_nodes'] = len(manager.nodes)
        rank = {v: i for i, v in enumerate(order)}
        answers = {0: None, 1: {}}
        # Frames: root, variable, branch edge, phase. No Python recursion in DFS.
        stack = [(root, None, None, 0)]
        while stack:
            edge, variable, child, phase = stack[-1]
            if phase == 0:
                if edge in answers:
                    stats['memo_hits'] += 1
                    stack.pop()
                    continue
                if max_states is not None and stats['expanded_states'] >= max_states:
                    raise BudgetExceeded("expanded state budget")
                stats['expanded_states'] += 1
                variable = min(manager.supports[abs(edge)], key=rank.__getitem__)
                histogram = stats['states_by_variable']
                key = str(variable)
                histogram[key] = histogram.get(key, 0) + 1
                child = manager.cofactor(edge, variable, False)
                stack[-1] = (edge, variable, child, 1)
                stack.append((child, None, None, 0))
            elif phase == 1:
                if answers[child] is not None:
                    answers[edge] = {**answers[child], variable: False}
                    stack.pop()
                else:
                    child = manager.cofactor(edge, variable, True)
                    stack[-1] = (edge, variable, child, 2)
                    stack.append((child, None, None, 0))
            else:
                answers[edge] = (None if answers[child] is None else
                                 {**answers[child], variable: True})
                stack.pop()
        if answers[root] is None:
            result['status'] = 'UNSAT'
        else:
            result['status'] = 'SAT'
            result['assignment'] = {v: answers[root].get(v, False) for v in order}
    except BudgetExceeded as exc:
        result['reason'] = str(exc)
    stats.update(interned_nodes=len(manager.nodes), work_units=manager.work,
                 cofactor_node_visits=manager.cofactor_visits)
    return result


def solve_circuit(circuit, *, value=True, order=None, max_states=100_000,
                  max_nodes=200_000, max_work=5_000_000):
    """Decide whether the output can equal value; check any witness on the input."""
    if not isinstance(circuit, Circuit) or type(value) is not bool:
        raise ValueError("A Circuit and Boolean output requirement are required")

    def build(manager):
        root = manager.from_circuit(circuit)
        return root if value else complement(root)

    result = _solve(build, range(1, circuit.inputs + 1), order,
                    max_states, max_nodes, max_work)
    if result['status'] == 'SAT':
        assignment = result['assignment']
        values = tuple(assignment[i] for i in range(1, circuit.inputs + 1))
        if circuit.evaluate(values)[circuit.output - 1] != value:
            raise AssertionError("SAT witness failed original circuit evaluation")
    return result


def solve_cnf(clauses, *, order=None, max_states=100_000,
              max_nodes=200_000, max_work=5_000_000):
    """Decide CNF with arbitrary positive integer variable names and signed literals."""
    clauses = tuple(tuple(c) for c in clauses)
    if any(type(lit) is not int or lit == 0 for c in clauses for lit in c):
        raise ValueError("CNF literals must be nonzero integers")
    labels = sorted({abs(lit) for c in clauses for lit in c})

    def build(manager):
        variables = {v: manager.variable(v) for v in labels}
        return manager.conjunction(manager.disjunction(
            variables[abs(lit)] if lit > 0 else complement(variables[abs(lit)])
            for lit in clause) for clause in clauses)

    result = _solve(build, labels, order, max_states, max_nodes, max_work)
    if result['status'] == 'SAT':
        assignment = result['assignment']
        if not all(any(assignment[abs(lit)] == (lit > 0) for lit in c) for c in clauses):
            raise AssertionError("SAT witness failed original CNF evaluation")
    return result


def distributivity_miter(k, *, selectors=2):
    """Linear-size identically false circuit; selectors=1 is a factoring control.

    T = XOR_i (a_i AND b_i); s = u (or u XOR v).
    Output = (s AND T) XOR XOR_{i,j} (selector_j AND a_i AND b_i).
    Variable order in the input: a_1..a_k, selectors, b_1..b_k.
    """
    if type(k) is not int or k < 1 or type(selectors) is not int or selectors not in (1, 2):
        raise ValueError("Positive k and one or two selectors required")
    n, gates = 2 * k + selectors, []

    def gate(kind, *args):
        gates.append(Gate(kind, tuple(args)))
        return n + len(gates)

    def xor_chain(wires):
        result = wires[0]
        for wire in wires[1:]:
            result = gate('XOR', result, wire)
        return result

    monomials = [gate('AND', i, k + selectors + i) for i in range(1, k + 1)]
    selection = list(range(k + 1, k + selectors + 1))
    left = gate('AND', xor_chain(selection), xor_chain(monomials))
    right = xor_chain([gate('AND', s, m) for m in monomials for s in selection])
    output = gate('XOR', left, right)
    return Circuit(n, tuple(gates), output)
