#!/usr/bin/env python3
"""Bounded audit of Boolean evaluation in commuting idempotent F2 matrices.

This does not construct a complete polynomial-size SAT representation. A zero
matrix may miss satisfying assignments and is never reported as UNSAT here.
"""
import argparse
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.circuit_extensions import Circuit, Gate


def identity(d):
    return tuple(1 << i for i in range(d))


def add(a, b):
    return tuple(x ^ y for x, y in zip(a, b))


def multiply(a, b):
    rows = []
    for row in a:
        value = 0
        for i, other in enumerate(b):
            if row >> i & 1:
                value ^= other
        rows.append(value)
    return tuple(rows)


def vector_product(a, v):
    return sum(((row & v).bit_count() & 1) << i for i, row in enumerate(a))


def rank(a):
    pivots = {}
    for row in a:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def validate(variables):
    if not variables or not variables[0]:
        raise ValueError('Positive variable count and matrix dimension required')
    d = len(variables[0])
    for a in variables:
        if len(a) != d or any(type(row) is not int or not 0 <= row < 1 << d for row in a):
            raise ValueError('Invalid square F2 matrix')
        if multiply(a, a) != a:
            raise ValueError('Variable matrix is not idempotent')
    for a, b in combinations(variables, 2):
        if multiply(a, b) != multiply(b, a):
            raise ValueError('Variable matrices do not commute')


def atoms(variables):
    one = identity(len(variables[0]))
    result = []
    for word in product((0, 1), repeat=len(variables)):
        value = one
        for bit, a in zip(word, variables):
            value = multiply(value, a if bit else add(one, a))
        result.append(value)
    return result


def evaluate_table(table, projections):
    """Finite audit representation via disjoint atoms; exponential in variables."""
    value = tuple(0 for _ in projections[0])
    for i, projection in enumerate(projections):
        if table >> i & 1:
            value = add(value, projection)
    return value


def evaluate_circuit(circuit, variables):
    one = identity(len(variables[0]))
    wires = [None, *variables]
    for gate in circuit.gates:
        a = wires[gate.inputs[0]]
        if gate.kind == 'NOT':
            result = add(one, a)
        elif gate.kind == 'XOR':
            result = add(a, wires[gate.inputs[1]])
        else:
            result = multiply(a, wires[gate.inputs[1]])
        wires.append(result)
    return wires[circuit.output]


def extract_witness(variables, value):
    """Require validated variables and their Boolean formula's matrix value.

    None means only that this representation returned zero, not UNSAT.
    No atom enumeration or simultaneous diagonalization is used here.
    """
    d = len(value)
    v = next((sum((row >> j & 1) << i for i, row in enumerate(value))
              for j in range(d) if any(row >> j & 1 for row in value)), 0)
    if not v:
        return None
    assignment = []
    for a in variables:
        projected = vector_product(a, v)
        assignment.append(bool(projected))
        if projected:
            v = projected
    if vector_product(value, v) != v or any(
            vector_product(a, v) != (v if bit else 0)
            for bit, a in zip(assignment, variables)):
        raise AssertionError('Common eigenvector invariant failed')
    return tuple(assignment)


def index(word):
    result = 0
    for bit in word:
        result = 2 * result + int(bit)
    return result


def represented_words(variables):
    """Recover the represented assignments in polynomial time, without 2^n atoms.

    Variables must have passed validate. Each iteration removes a nonzero
    orthogonal projection, so at most d iterations are necessary.
    """
    d = len(variables[0])
    one = identity(d)
    remaining, words = one, []
    for _ in range(d):
        if not any(remaining):
            break
        word = extract_witness(variables, remaining)
        projection = one
        for bit, a in zip(word, variables):
            projection = multiply(projection, a if bit else add(one, a))
        if not any(projection) or multiply(remaining, projection) != projection:
            raise AssertionError('Selected atom is not in the remaining subspace')
        remaining = add(remaining, projection)
        words.append(word)
    if any(remaining):
        raise AssertionError('More represented assignments than matrix dimension')
    return tuple(words)


def audit():
    matrices = [(raw & 3, raw >> 2) for raw in range(16)]
    idempotents = [a for a in matrices if multiply(a, a) == a]
    rng = random.Random(20261106)
    circuits = []
    for _ in range(64):
        gates = []
        for _ in range(10):
            kind = rng.choice(('AND', 'XOR', 'NOT'))
            inputs = tuple(rng.randint(1, 3 + len(gates))
                           for _ in range(1 if kind == 'NOT' else 2))
            gates.append(Gate(kind, inputs))
        c = Circuit(3, tuple(gates), 13)
        truth = sum(int(c.evaluate(word)[c.output - 1]) << i
                    for i, word in enumerate(product((False, True), repeat=3)))
        circuits.append((c, truth))

    tuples = truth_checks = extracted = missed_sat = circuit_checks = 0
    support_histogram = {}
    failure_example = None
    for variables in product(idempotents, repeat=3):
        if any(multiply(a, b) != multiply(b, a) for a, b in combinations(variables, 2)):
            continue
        validate(variables)
        tuples += 1
        projections = atoms(variables)
        support = [i for i, a in enumerate(projections) if any(a)]
        recovered = represented_words(variables)
        if len(recovered) != len(support) or sorted(map(index, recovered)) != support:
            raise AssertionError('Polynomial support extraction disagrees with exhaustive atoms')
        support_histogram[str(len(support))] = support_histogram.get(str(len(support)), 0) + 1
        summed = (0, 0)
        for a in projections:
            summed = add(summed, a)
            if multiply(a, a) != a:
                raise AssertionError('Atom is not a projection')
        if (summed != identity(2) or sum(rank(a) for a in projections) != 2
                or len(support) > 2
                or any(any(multiply(a, b)) for a, b in combinations(projections, 2))):
            raise AssertionError('Direct-sum classification failed')
        missing = next(i for i in range(8) if i not in support)
        if failure_example is None:
            failure_example = dict(variable_matrices=variables,
                                   represented_assignments=support,
                                   missed_singleton_assignment=missing)
        for truth in range(256):
            value = evaluate_table(truth, projections)
            detected = any(truth >> i & 1 for i in support)
            if bool(any(value)) != detected:
                raise AssertionError('Evaluation disagrees with represented assignments')
            witness = extract_witness(variables, value)
            if detected:
                if witness is None or not (truth >> index(witness) & 1):
                    raise AssertionError('Extracted word is not a satisfying assignment')
                extracted += 1
            elif witness is not None:
                raise AssertionError('Witness returned for zero representation')
            if truth and not detected:
                missed_sat += 1
            truth_checks += 1
        for circuit, truth in circuits:
            value = evaluate_circuit(circuit, variables)
            if value != evaluate_table(truth, projections):
                raise AssertionError('Original gate semantics disagree with atom decomposition')
            witness = extract_witness(variables, value)
            if witness is not None and not circuit.evaluate(witness)[circuit.output - 1]:
                raise AssertionError('Witness fails original circuit')
            circuit_checks += 1

    full = tuple(tuple((1 << j) if j >> (2 - i) & 1 else 0 for j in range(8))
                 for i in range(3))
    validate(full)
    projections = atoms(full)
    if sorted(map(index, represented_words(full))) != list(range(8)):
        raise AssertionError('Full representation support extraction failed')
    for truth in range(256):
        value = evaluate_table(truth, projections)
        witness = extract_witness(full, value)
        if bool(any(value)) != bool(truth) or (truth and
                (witness is None or not (truth >> index(witness) & 1))):
            raise AssertionError('Full exponential-dimension control failed')

    p, q, non_idempotent = (3, 0), (1, 1), (2, 0)
    for bad in ((p, q), (non_idempotent,)):
        try:
            validate(bad)
        except ValueError:
            pass
        else:
            raise AssertionError('An invalid representation was accepted')
    if any(multiply(p, q)) or not any(multiply(q, p)):
        raise AssertionError('Noncommutativity failure control changed')

    return dict(all_checks_passed=True, dimension=2, variables=3,
                idempotent_matrices=len(idempotents), commuting_tuples=tuples,
                represented_assignment_histogram=support_histogram,
                truth_function_checks=truth_checks, satisfying_witnesses_checked=extracted,
                polynomial_support_extractions_checked=tuples + 1,
                satisfiable_functions_missed=missed_sat, original_circuit_checks=circuit_checks,
                explicit_failure=failure_example,
                full_representation_control=dict(dimension=8, truth_functions_checked=256),
                invalid_representation_controls=dict(noncommuting=True, nonidempotent=True),
                zero_matrix_means='UNKNOWN unless completeness is proved separately',
                formula_independent_polynomial_dimension_refuted=True,
                efficient_formula_dependent_constructor_found=False,
                p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), sort_keys=True, indent=2) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'boolean_matrix_sat.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
