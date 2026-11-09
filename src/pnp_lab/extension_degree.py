"""Bounded F2 coordinate expansion for the extension-substitution audit.

Ordinary products retain repeated variables. Squarefree reduction is explicit;
it is used to choose coordinate functions, never as a free PC proof rule.
"""
from .circuit_extensions import Circuit, Gate

ZERO = frozenset()
ONE = frozenset({()})


class ExpansionLimit(ValueError):
    pass


def ordinary_product(left, right):
    result = set()
    for a in left:
        for b in right:
            term = tuple(sorted((*a, *b)))
            if term in result:
                result.remove(term)
            else:
                result.add(term)
    return frozenset(result)


def squarefree(polynomial):
    result = set()
    for term in polynomial:
        reduced = tuple(sorted(set(term)))
        if reduced in result:
            result.remove(reduced)
        else:
            result.add(reduced)
    return frozenset(result)


def degree(polynomial):
    return max(map(len, polynomial), default=0)


def evaluate(polynomial, word):
    return sum(all(word[v-1] for v in term) for term in polynomial) % 2


def expand(circuit, *, max_terms=20000, max_work=100000):
    """Return squarefree coordinates or explicitly fail a resource bound."""
    if any(type(cap) is not int or cap < 0 for cap in (max_terms, max_work)):
        raise ValueError('Nonnegative expansion budgets required')
    if circuit.variables > max_work or max_terms < 1:
        raise ExpansionLimit('coordinate initialization budget')
    coordinates = [frozenset({(i,)}) for i in range(1, circuit.inputs+1)]
    depths = [0] * circuit.inputs
    work = circuit.inputs
    for gate in circuit.gates:
        a = coordinates[gate.inputs[0]-1]
        depth = depths[gate.inputs[0]-1]
        if gate.kind == 'NOT':
            cost = len(a) + 1
        else:
            b = coordinates[gate.inputs[1]-1]
            depth = max(depth, depths[gate.inputs[1]-1])
            cost = len(a)*len(b) if gate.kind == 'AND' else len(a)+len(b)
        work += cost
        if work > max_work:
            raise ExpansionLimit('coordinate expansion work budget')
        if gate.kind == 'NOT':
            q = ONE ^ a
        elif gate.kind == 'AND':
            q = squarefree(ordinary_product(a, b))
            depth += 1
        else:
            q = a ^ b
        if len(q) > max_terms:
            raise ExpansionLimit('coordinate polynomial term budget')
        coordinates.append(q)
        depths.append(depth)
    return dict(coordinates=tuple(coordinates), work=work,
                coordinate_degree=max(map(degree, coordinates)),
                output_degree=degree(coordinates[circuit.output-1]),
                output_terms=len(coordinates[circuit.output-1]),
                multiplication_depth=max(depths))


def gate_residuals(circuit, coordinates):
    """Ordinary images of the gate equations; they need not be zero polynomials."""
    result = []
    for output, gate in enumerate(circuit.gates, circuit.inputs+1):
        a = coordinates[gate.inputs[0]-1]
        if gate.kind == 'NOT':
            rhs = ONE ^ a
        else:
            b = coordinates[gate.inputs[1]-1]
            rhs = ordinary_product(a, b) if gate.kind == 'AND' else a ^ b
        result.append(coordinates[output-1] ^ rhs)
    return tuple(result)


def reduction_circuit(n, operation, *, balanced=False):
    """An explicit n-input AND, OR or XOR circuit in the AND/XOR/NOT basis."""
    if type(n) is not int or n < 1 or operation not in ('AND', 'OR', 'XOR'):
        raise ValueError('Positive n and AND/OR/XOR required')
    gates = []
    def emit(kind, inputs):
        gates.append(Gate(kind, tuple(inputs)))
        return n + len(gates)
    def combine(a, b):
        if operation == 'OR':
            # a OR b = NOT ((NOT a) AND (NOT b)).
            na, nb = emit('NOT', (a,)), emit('NOT', (b,))
            return emit('NOT', (emit('AND', (na, nb)),))
        return emit(operation, (a, b))
    wires = list(range(1, n+1))
    if balanced:
        while len(wires) > 1:
            wires = [combine(wires[i], wires[i+1]) if i+1 < len(wires) else wires[i]
                     for i in range(0, len(wires), 2)]
        output = wires[0]
    else:
        output = wires[0]
        for wire in wires[1:]:
            output = combine(output, wire)
    return Circuit(n, tuple(gates), output)
