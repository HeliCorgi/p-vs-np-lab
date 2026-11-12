#!/usr/bin/env python3
"""A checked SAT-to-cubic-sign-sum bridge and the quadratic elimination control.

These are standard character-orthogonality and quadratic Gauss-sum arguments,
not claimed as new results. The new research attempt is to obtain a fast
ZERO TEST for the resulting cubic sum; that core algorithm is not supplied.

For an n-input AND/XOR/NOT circuit with g gates, introduce its g gate-value
variables y. Each gate has a quadratic Boolean equation q_j(x,y)=0; append
the linear equation output+1=0. There are t=g+1 equations. Introduce t new
multiplier bits z and the sparse degree-at-most-three polynomial

    P(x,y,z) = XOR_j z_j*q_j(x,y) over F2.

There are N=n+2g+1 variables and at most 3g+2 monomials. Orthogonality gives
sum_z (-1)^P = 2^t when every q_j=0, and zero otherwise. The circuit has a
unique consistent y for each x, so

    Gap(P) = sum_{x,y,z} (-1)^P = 2^(g+1) * #SAT(circuit).

In particular the reduced sum is nonnegative, and testing whether it is zero
would decide SAT. All construction work is polynomial in the explicit circuit
encoding. The reduction does not compute the sum by itself. Its exponential
reference enumeration is used only for small, budgeted validation cases.

Quadratic phases have a polynomial elimination: write
P=uv+u*A(w)+v*B(w)+R(w), with A,B affine. Summing over u,v yields
2*(-1)^(R+A*B); the residual remains quadratic. An uncoupled nonzero linear
term makes the final gap zero. This control is complete for quadratic phases.
For cubic phases the coefficient of uv can depend on w. Treating it as 1 is
already wrong for P=uvw: its gap is 6, whereas that invalid substitution gives
4. The quadratic control explicitly rejects cubic inputs. No claimed general
SAT algorithm or lower bound follows from its success.

This faulty step also fails INSIDE the reduced circuit family, not just for an
arbitrary cubic. The one-gate circuit output=x AND y gives
P=z1*(w+x*y)+z2*(w+1), with true gap 4. Eliminating x,y as though their
coefficient z1 were constantly 1 would return
2*sum_{w,z1,z2} (-1)^(z1*w+z2*w+z2)=0, falsely declaring UNSAT.
This rejects that specific substitution, not every possible cubic algorithm.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.circuit_extensions import Circuit, Gate
from pnp_lab.sat_scaling import satisfies, validate


class PhaseBudgetExceeded(RuntimeError):
    pass


def _polynomial(n, terms):
    if type(n) is not int or n < 0:
        raise ValueError('nonnegative variable count required')
    result = set()
    for term in terms:
        if type(term) is not int or term < 0 or term.bit_length() > n:
            raise ValueError('invalid squarefree monomial bit mask')
        result.symmetric_difference_update((term,))
    return result


def circuit_phase(circuit):
    """Construct quadratic constraints and their cubic Lagrange-multiplier phase."""
    base = circuit.variables
    constraints = []
    for output, gate in enumerate(circuit.gates, circuit.inputs + 1):
        out = 1 << (output - 1)
        operands = [1 << (wire - 1) for wire in gate.inputs]
        if gate.kind == 'AND':
            raw = [out, operands[0] | operands[1]]
        elif gate.kind == 'XOR':
            raw = [out, *operands]
        else:
            raw = [out, operands[0], 0]
        constraints.append(_polynomial(base, raw))
    constraints.append({1 << (circuit.output - 1), 0})
    terms = set()
    for j, constraint in enumerate(constraints):
        multiplier = 1 << (base + j)
        terms.symmetric_difference_update(mask | multiplier for mask in constraint)
    n = base + len(constraints)
    if any(mask.bit_count() > 3 for mask in terms) or len(terms) > 3*len(circuit.gates)+2:
        raise AssertionError('phase construction exceeded its degree or size bound')
    return dict(variables=n, terms=sorted(terms), constraints=[sorted(q) for q in constraints],
                multiplier_count=len(constraints), scale=1 << len(constraints))


def cnf_circuit(n, clauses):
    """Uniform shared AND/XOR/NOT circuit; no Boolean-equivalence oracle."""
    clauses = tuple(tuple(c) for c in clauses)
    validate(n, clauses)
    if n < 1 or any(len(c) > 3 for c in clauses):
        raise ValueError('positive input count and width at most three required')
    gates, known = [], {}

    def add(kind, *inputs):
        key = (kind, inputs)
        if key not in known:
            gates.append(Gate(kind, inputs))
            known[key] = n + len(gates)
        return known[key]

    zero = add('XOR', 1, 1)
    one = add('NOT', zero)
    terms = []
    for clause in clauses:
        literals = [lit if lit > 0 else add('NOT', -lit) for lit in clause]
        row = literals[0] if literals else zero
        for lit in literals[1:]:
            row = add('XOR', add('XOR', row, lit), add('AND', row, lit))
        terms.append(row)
    output = terms[0] if terms else one
    for term in terms[1:]:
        output = add('AND', output, term)
    return Circuit(n, tuple(gates), output)


def evaluate(terms, word):
    return sum((word & term) == term for term in terms) % 2


def exact_gap(n, terms, *, assignment_limit=1 << 18):
    """Exponential reference evaluation, never represented as a fast zero test."""
    terms = _polynomial(n, terms)
    if type(assignment_limit) is not int or assignment_limit < 0:
        raise ValueError('nonnegative enumeration budget required')
    if n >= assignment_limit.bit_length():
        raise PhaseBudgetExceeded('phase assignment enumeration budget')
    return sum(1 - 2*evaluate(terms, word) for word in range(1 << n))


def quadratic_gap(n, terms):
    """Exact polynomial elimination, restricted to quadratic Boolean phases."""
    terms = _polynomial(n, terms)
    if any(term.bit_count() > 2 for term in terms):
        raise ValueError('quadratic elimination cannot accept a cubic phase')
    remaining, factor, steps, maximum = n, 1, 0, len(terms)
    while True:
        pair = next((term for term in sorted(terms) if term.bit_count() == 2), None)
        if pair is None:
            gap = 0 if any(term != 0 for term in terms) else factor*(1 << remaining)*(-1 if 0 in terms else 1)
            return dict(gap=gap, eliminated_pairs=steps, maximum_terms=maximum)
        u = pair & -pair
        v = pair ^ u
        a, b, residual = set(), set(), set()
        for term in terms:
            if term == pair:
                continue
            if term & u:
                a.add(term ^ u)
            elif term & v:
                b.add(term ^ v)
            else:
                residual.add(term)
        for left in a:
            for right in b:
                residual.symmetric_difference_update((left | right,))
        if any(term & pair for term in residual):
            raise AssertionError('eliminated coordinate remained in the residual')
        terms = residual
        factor *= 2
        remaining -= 2
        steps += 1
        maximum = max(maximum, len(terms))


def audit():
    rng = random.Random(90109)
    circuits = [Circuit(1, (), 1), Circuit(1, (Gate('NOT', (1,)),), 2),
                Circuit(1, (Gate('XOR', (1, 1)),), 2),
                Circuit(2, (Gate('AND', (1, 2)),), 3)]
    for n in (1, 2, 3):
        for _ in range(10):
            gates = []
            for j in range(3):
                kind = rng.choice(('AND', 'XOR', 'NOT'))
                wires = tuple(rng.randrange(1, n+j+1) for _ in range(1 if kind == 'NOT' else 2))
                gates.append(Gate(kind, wires))
            circuits.append(Circuit(n, tuple(gates), n+3))
    rows = []
    for circuit in circuits:
        phase = circuit_phase(circuit)
        count = sum(circuit.evaluate(bits)[circuit.output-1] for bits in product((False, True), repeat=circuit.inputs))
        gap = exact_gap(phase['variables'], phase['terms'])
        if gap != phase['scale'] * count:
            raise AssertionError('SAT-to-cubic-phase identity failed')
        rows.append(dict(inputs=circuit.inputs, gates=[dict(kind=g.kind, inputs=g.inputs) for g in circuit.gates],
                         output=circuit.output, phase=phase, satisfying_inputs=count, exact_gap=gap))
    quadratic_cases = quadratic_assignments = 0
    for n in range(8):
        universe = [mask for mask in range(1 << n) if mask.bit_count() <= 2]
        for _ in range(16):
            terms = [mask for mask in universe if rng.randrange(2)]
            if quadratic_gap(n, terms)['gap'] != exact_gap(n, terms):
                raise AssertionError('quadratic control disagrees with exhaustive evaluation')
            quadratic_cases += 1
            quadratic_assignments += 1 << n
    cnf_cases = 0
    for n in range(1, 6):
        for _ in range(16):
            clauses = [tuple(v if rng.randrange(2) else -v for v in
                             rng.sample(range(1, n+1), rng.randrange(min(n, 3)+1)))
                       for _ in range(rng.randrange(8))]
            circuit = cnf_circuit(n, clauses)
            for bits in product((False, True), repeat=n):
                word = sum(int(b) << i for i, b in enumerate(bits))
                if circuit.evaluate(bits)[circuit.output-1] != satisfies(clauses, word):
                    raise AssertionError('CNF-to-circuit coverage failed')
            cnf_cases += 1
    example = exact_gap(3, [7])
    if example != 6:
        raise AssertionError('cubic obstruction failed')
    and_phase = circuit_phase(Circuit(2, (Gate('AND', (1, 2)),), 3))
    and_gap = exact_gap(and_phase['variables'], and_phase['terms'])
    invalid_and_gap = 2*exact_gap(3, [3, 5, 4])
    if and_gap != 4 or invalid_and_gap != 0:
        raise AssertionError('obstruction inside the reduced circuit family failed')
    circuit_assignments = sum(1 << row['phase']['variables'] for row in rows)
    control_assignments = quadratic_assignments + 8 + (1 << and_phase['variables']) + 8
    return dict(all_checks_passed=True, circuit_cases=rows, quadratic_cases=quadratic_cases,
                cnf_to_circuit_cases=cnf_cases,
                circuit_phase_assignments_enumerated=circuit_assignments,
                control_phase_assignments_enumerated=control_assignments,
                phase_assignments_enumerated=circuit_assignments+control_assignments,
                cubic_control=dict(polynomial='x*y*z', actual_gap=example,
                                   invalid_constant_coefficient_elimination_prediction=4),
                reduced_circuit_control=dict(circuit='output=x AND y', phase=and_phase,
                    polynomial='z1*(w+x*y)+z2*(w+1)', actual_gap=and_gap,
                    invalid_constant_coefficient_elimination_prediction=invalid_and_gap,
                    false_decision='UNSAT on a satisfiable one-gate circuit'),
                uniform_reduction='N=n+2g+1 variables, degree at most 3, at most 3g+2 monomials; Gap=2^(g+1)*#SAT.',
                remaining_core='A deterministic polynomial-time zero test on the reduced sparse cubic phases; not supplied.',
                polynomial_cubic_zero_test_obtained=False, p_vs_np_resolved=False,
                scope='Known character-orthogonality and quadratic Gauss-sum constructions, checked here on finite inputs. '
                      'The quadratic algorithm rejects cubic inputs. No novel separation, general SAT algorithm or Lean claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), indent=2, sort_keys=True) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'cubic_phase_sat.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
