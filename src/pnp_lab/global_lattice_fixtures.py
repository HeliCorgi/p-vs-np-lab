"""Carry cycles whose obstruction is global integer torsion.

The solver receives only a signed, permuted width-three CNF.  Gate and wire
metadata in this module are construction/audit data, never discovery hints.
Every gate has a saturated integer affine hull.  Long private equality paths
keep small raw local scopes from seeing more than one gate in a component.
"""
from math import isqrt


def carry_gate(a, x, b, carry):
    """Four clauses for the Boolean relation a + x - b = carry."""
    if (any(type(v) is not int or v < 1 for v in (a, x, b)) or
            len({a, x, b}) != 3 or type(carry) is not int or carry not in (0, 1)):
        raise ValueError('invalid carry gate')
    rows = ((-a, b), (-x, b), (a, x, -b), (-a, -x))
    return rows if carry == 0 else tuple(tuple(-l for l in c) for c in rows)


def carry_cycle(m, total, *, wire_length=10):
    """Return n, raw CNF, a SAT word when total is 0 or m, and audit metadata.

    The full exact equations reduce to m*x=total, with a free initial counter.
    Each private wire has ``wire_length`` edges and distinct internal bits.
    The number of variables is 3*m + (2*m-1)*(wire_length-1).
    """
    if type(m) is not int or m < 2:
        raise ValueError('at least two gates required')
    if type(total) is not int or not 0 <= total <= m:
        raise ValueError('total must be between zero and the number of gates')
    if type(wire_length) is not int or wire_length < 1:
        raise ValueError('positive wire length required')
    carries = tuple((i+1)*total//m - i*total//m for i in range(m))
    gates = tuple((3*i+1, 3*i+2, 3*i+3, carries[i]) for i in range(m))
    rows = [c for a, x, b, carry in gates for c in carry_gate(a, x, b, carry)]
    n = 3*m
    wires = []

    def wire(start, end):
        nonlocal n
        path = (start, *range(n+1, n+wire_length), end)
        n += wire_length-1
        wires.append(path)
        for u, v in zip(path, path[1:]):
            rows.extend(((-u, v), (u, -v)))

    # Each counter output becomes the next gate's input, cyclically.
    for i, (_, _, b, _) in enumerate(gates):
        wire(b, gates[(i+1) % m][0])
    # Common x is carried along a path, avoiding an unnecessary redundant cycle.
    for (_, x, _, _), (_, y, _, _) in zip(gates, gates[1:]):
        wire(x, y)
    metadata = dict(gates=gates, wires=tuple(wires), carries=carries,
                    gate_count=m, total=total, wire_length=wire_length)
    word = None
    if total in (0, m):
        values = [0]*n
        for _, x, _, _ in gates:
            values[x-1] = int(total == m)
        for path in wires:
            for v in path[1:-1]:
                values[v-1] = values[path[0]-1]
        word = sum(v << i for i, v in enumerate(values))
        assert all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in rows)
    return n, tuple(rows), word, metadata


def carry_field_values(n, metadata, prime):
    """A field-valued solution of the gate/wire equations, or None.

    This is an audit of a relaxation, not a Boolean SAT witness.  For a prime
    dividing m it exists exactly when that prime also divides total.
    """
    if (type(prime) is not int or prime < 2 or
            any(prime % d == 0 for d in range(2, isqrt(prime)+1))):
        raise ValueError('prime characteristic required')
    m, total = metadata['gate_count'], metadata['total']
    if m % prime == 0:
        if total % prime:
            return None
        value = 0
    else:
        value = total * pow(m, -1, prime) % prime
    out = [0]*n
    current = 0
    for a, x, b, carry in metadata['gates']:
        out[a-1], out[x-1] = current, value
        current = (current + value - carry) % prime
        out[b-1] = current
    assert current == 0
    for path in metadata['wires']:
        assert out[path[0]-1] == out[path[-1]-1]
        for v in path[1:-1]:
            out[v-1] = out[path[0]-1]
    assert all((out[a-1]+out[x-1]-out[b-1]-carry) % prime == 0
               for a, x, b, carry in metadata['gates'])
    return tuple(out)


def carry_integer_solution_exists(m, total):
    """Exact feasibility criterion for the equations, without Boolean bounds."""
    if type(m) is not int or m < 2 or type(total) is not int:
        raise ValueError('invalid equation')
    return total % m == 0
