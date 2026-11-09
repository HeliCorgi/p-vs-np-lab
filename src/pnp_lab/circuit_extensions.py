"""Tseitin circuits and checked refutations of two identical circuit copies.

This is a structural family refuter, not a general SAT or circuit-equivalence
algorithm. The final certificate uses only ordinary resolution on input CNF.
"""
from dataclasses import dataclass
from functools import lru_cache

from .resolution_closure import KIND, check_resolution


@dataclass(frozen=True)
class Gate:
    kind: str
    inputs: tuple[int, ...]


@dataclass(frozen=True)
class Circuit:
    inputs: int
    gates: tuple[Gate, ...]
    output: int

    def __post_init__(self):
        if type(self.inputs) is not int or self.inputs < 1:
            raise ValueError('Positive input count required')
        for i, gate in enumerate(self.gates, self.inputs + 1):
            arity = {'AND': 2, 'XOR': 2, 'NOT': 1}.get(gate.kind)
            if arity is None or len(gate.inputs) != arity:
                raise ValueError('Unknown gate or incorrect arity')
            if any(type(w) is not int or not 1 <= w < i for w in gate.inputs):
                raise ValueError('Gates must refer to earlier wires')
        if type(self.output) is not int or not 1 <= self.output <= self.variables:
            raise ValueError('Invalid output wire')

    @property
    def variables(self):
        return self.inputs + len(self.gates)

    def evaluate(self, values):
        if len(values) != self.inputs or any(type(v) is not bool for v in values):
            raise ValueError('One Boolean per original input required')
        wires = [False, *values]
        for gate in self.gates:
            a = wires[gate.inputs[0]]
            if gate.kind == 'NOT':
                value = not a
            else:
                b = wires[gate.inputs[1]]
                value = a and b if gate.kind == 'AND' else a != b
            wires.append(value)
        return tuple(wires[1:])


def inner_product(m):
    if type(m) is not int or m < 1:
        raise ValueError('m must be a positive integer')
    gates = [Gate('AND', (i + 1, m + i + 1)) for i in range(m)]
    output = 2 * m + 1
    for i in range(1, m):
        gates.append(Gate('XOR', (output, 2 * m + i + 1)))
        output = 2 * m + len(gates)
    return Circuit(2 * m, tuple(gates), output)


def _clauses(kind, inputs, z):
    a = inputs[0]
    if kind == 'NOT':
        return ((a, z), (-a, -z))
    b = inputs[1]
    if kind == 'AND':
        return ((-z, a), (-z, b), (z, -a, -b))
    if kind == 'XOR':
        return ((a, b, -z), (-a, -b, -z), (a, -b, z), (-a, b, z))
    raise ValueError('Unknown gate')


def tseitin(circuit, value=True):
    """Unique-extension encoding, with an explicit Boolean output requirement."""
    if type(value) is not bool:
        raise ValueError('Output requirement must be Boolean')
    cs = []
    for z, gate in enumerate(circuit.gates, circuit.inputs + 1):
        cs.extend(_clauses(gate.kind, gate.inputs, z))
    cs.append((circuit.output if value else -circuit.output,))
    return circuit.variables, tuple(cs)


def duplicate_miter(circuit):
    """Two disjoint sets of gate wires, shared inputs, opposite output units."""
    size = len(circuit.gates)
    rename = lambda w: w if w <= circuit.inputs else w + size
    cs = []
    gate_sources = []
    for z, gate in enumerate(circuit.gates, circuit.inputs + 1):
        start = len(cs)
        cs.extend(_clauses(gate.kind, gate.inputs, z))
        cs.extend(_clauses(gate.kind, tuple(map(rename, gate.inputs)), rename(z)))
        gate_sources.append(tuple(range(start, len(cs))))
    cs.extend(((circuit.output,), (-rename(circuit.output),)))
    return circuit.inputs + 2 * size, tuple(cs), tuple(gate_sources)


def _ordered(row):
    return tuple(sorted(row, key=lambda x: (abs(x), x)))


@lru_cache(maxsize=128)
def _local_template(clauses, targets):
    """Saturate at most six variables. Record every retained row and pair tried.

    This search is never run on the global input-variable set. Its row bound
    is 3**6, independent of circuit size. Prune only after deriving targets.
    """
    variables = {abs(l) for c in clauses for l in c}
    if len(variables) > 6:
        raise ValueError('Gate-local search exceeded six variables')
    rows, nodes, known = [], [], {}
    def add(row, node):
        if row in known or any(-x in row for x in row):
            return
        known[row] = len(rows)
        rows.append(row)
        nodes.append(node)
    for i, c in enumerate(clauses):
        add(frozenset(c), ('input', i))
    wanted = tuple(map(frozenset, targets))
    def target_roots():
        return tuple(next((j for j, row in enumerate(rows) if row <= t), None)
                     for t in wanted)
    i = pairs = 0
    while any(r is None for r in target_roots()):
        if i == len(rows):
            raise RuntimeError('Gate congruence targets not derivable')
        a = rows[i]
        for j in range(i):
            b = rows[j]
            pairs += 1
            for p in _ordered(a):
                if -p in b:
                    add((a - {p}) | (b - {-p}), ('resolve', i, j, p))
        i += 1
    roots = target_roots()
    needed, stack = set(roots), list(roots)
    while stack:
        node = nodes[stack.pop()]
        if node[0] == 'resolve':
            for parent in node[1:3]:
                if parent not in needed:
                    needed.add(parent)
                    stack.append(parent)
    indices = sorted(needed)
    remap = {old: new for new, old in enumerate(indices)}
    compact = tuple(nodes[j] if nodes[j][0] == 'input' else
                    ('resolve', remap[nodes[j][1]], remap[nodes[j][2]], nodes[j][3])
                    for j in indices)
    return compact, tuple(remap[r] for r in roots), len(rows), pairs


def refute_duplicate(circuit):
    """Construct an ordinary-resolution proof, checked against original CNF.

    The correspondence is supplied by the duplicate-circuit constructor; no
    arbitrary-CNF recognition or semantic circuit-equivalence claim is made.
    """
    n, cs, sources = duplicate_miter(circuit)
    nodes, rows, input_nodes = [], [], {}
    for i, clause in enumerate(cs):
        row = frozenset(clause)
        if any(-l in row for l in row):
            continue
        input_nodes[i] = len(nodes)
        nodes.append(dict(op='input', clause=i))
        rows.append(row)
    size = len(circuit.gates)
    rename = lambda w: w if w <= circuit.inputs else w + size
    equalities = {}
    stats = dict(gate_pairs=size, local_rows_bound_sum=0, local_pairs_bound_sum=0,
                 max_local_variables=0)
    def resolve(a, b, p):
        if p not in rows[a] or -p not in rows[b]:
            raise AssertionError('Invalid generated pivot')
        row = (rows[a] - {p}) | (rows[b] - {-p})
        nodes.append(dict(op='resolve', left=a, right=b, pivot=p))
        rows.append(row)
        return len(rows) - 1
    for offset, gate in enumerate(circuit.gates):
        z = circuit.inputs + offset + 1
        premises = [input_nodes[i] for i in sources[offset] if i in input_nodes]
        for w in dict.fromkeys(gate.inputs):
            if w > circuit.inputs:
                premises.extend(equalities[w])
        wires = sorted({abs(l) for p in premises for l in rows[p]})
        local = {w: i + 1 for i, w in enumerate(wires)}
        to_local = lambda l: local[abs(l)] * (1 if l > 0 else -1)
        to_global = lambda l: wires[abs(l)-1] * (1 if l > 0 else -1)
        targets = ((-z, rename(z)), (z, -rename(z)))
        template, roots, row_count, pair_count = _local_template(
            tuple(_ordered(map(to_local, rows[p])) for p in premises),
            tuple(tuple(map(to_local, t)) for t in targets))
        instantiated = []
        for node in template:
            if node[0] == 'input':
                instantiated.append(premises[node[1]])
            else:
                instantiated.append(resolve(instantiated[node[1]], instantiated[node[2]],
                                            to_global(node[3])))
        equalities[z] = tuple(instantiated[r] for r in roots)
        stats['local_rows_bound_sum'] += row_count
        stats['local_pairs_bound_sum'] += pair_count
        stats['max_local_variables'] = max(stats['max_local_variables'], len(wires))
    positive, negative = input_nodes[len(cs)-2], input_nodes[len(cs)-1]
    if circuit.output > circuit.inputs:
        implication = equalities[circuit.output][0]
        positive = (resolve(positive, implication, circuit.output)
                    if -circuit.output in rows[implication] else implication)
    if rows[positive]:
        resolve(positive, negative, rename(circuit.output))
    certificate = dict(kind=KIND, width=max(map(len, rows)), nodes=nodes, root=len(nodes)-1)
    if not check_resolution(n, cs, certificate):
        raise AssertionError('Independent resolution checker rejected construction')
    stats.update(proof_nodes=len(nodes), proof_width=certificate['width'])
    return dict(variables=n, clauses=cs, certificate=certificate, stats=stats)
