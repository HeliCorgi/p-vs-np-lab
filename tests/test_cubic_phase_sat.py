"""Check the bridge against Boolean semantics and independent truth tables."""
from itertools import product
import unittest

from experiments.cubic_phase_sat import (
    PhaseBudgetExceeded, circuit_phase, cnf_circuit, exact_gap, quadratic_gap,
)
from pnp_lab.circuit_extensions import Circuit, Gate


def truth_sign(terms, bits):
    value = 0
    for mask in terms:
        value ^= int(all(bit for j, bit in enumerate(bits) if mask & (1 << j)))
    return 1 - 2*value


def truth_gap(n, terms):
    return sum(truth_sign(terms, bits) for bits in product((False, True), repeat=n))


class CubicPhaseTests(unittest.TestCase):
    def test_every_quadratic_polynomial_through_three_variables(self):
        for n in range(4):
            universe = [mask for mask in range(1 << n) if mask.bit_count() <= 2]
            for choices in product((False, True), repeat=len(universe)):
                terms = [mask for mask, present in zip(universe, choices) if present]
                expected = truth_gap(n, terms)
                self.assertEqual(exact_gap(n, terms), expected)
                self.assertEqual(quadratic_gap(n, terms)['gap'], expected)

    def test_gate_equations_and_orthogonality_for_every_base_assignment(self):
        circuits = [Circuit(2, (), 1)]
        for kind in ('AND', 'XOR', 'NOT'):
            for inputs in ((1,), (2,)) if kind == 'NOT' else product((1, 2), repeat=2):
                circuits.append(Circuit(2, (Gate(kind, tuple(inputs)),), 3))
        # Shared intermediates, an output that is not the last gate, and unused gates.
        circuits.extend([
            Circuit(2, (Gate('AND', (1, 2)), Gate('XOR', (3, 1)), Gate('NOT', (4,))), 5),
            Circuit(2, (Gate('AND', (1, 2)), Gate('NOT', (3,))), 1),
        ])
        for circuit in circuits:
            phase = circuit_phase(circuit)
            t = len(circuit.gates) + 1
            self.assertEqual(phase['variables'], circuit.inputs + 2*len(circuit.gates) + 1)
            self.assertLessEqual(len(phase['terms']), 3*len(circuit.gates)+2)
            self.assertTrue(all(mask.bit_count() <= 3 for mask in phase['terms']))
            for base in product((False, True), repeat=circuit.variables):
                equations = []
                for j, gate in enumerate(circuit.gates, circuit.inputs):
                    operands = [base[wire-1] for wire in gate.inputs]
                    expected = (all(operands) if gate.kind == 'AND' else
                                operands[0] != operands[1] if gate.kind == 'XOR' else
                                not operands[0])
                    equations.append(base[j] == expected)
                equations.append(base[circuit.output-1])
                self.assertEqual([truth_sign(q, base) == 1 for q in phase['constraints']], equations)
                summed = sum(truth_sign(phase['terms'], base + z)
                             for z in product((False, True), repeat=t))
                self.assertEqual(summed, (1 << t) if all(equations) else 0)

    def test_circuit_count_identity_with_sharing_constants_and_unused_inputs(self):
        circuits = [Circuit(3, (), 1)]
        for kind, inputs in [('AND', (1, 2)), ('AND', (1, 1)), ('XOR', (1, 1)), ('NOT', (1,))]:
            circuits.append(Circuit(2, (Gate(kind, inputs),), 3))
        circuits.extend([
            Circuit(2, (Gate('AND', (1, 2)), Gate('XOR', (3, 3))), 4),
            Circuit(1, (Gate('XOR', (1, 1)), Gate('NOT', (2,))), 3),
            Circuit(2, (Gate('AND', (1, 2)), Gate('NOT', (3,))), 1),
        ])
        for circuit in circuits:
            phase = circuit_phase(circuit)
            count = sum(circuit.evaluate(bits)[circuit.output-1]
                        for bits in product((False, True), repeat=circuit.inputs))
            self.assertEqual(truth_gap(phase['variables'], phase['terms']), phase['scale']*count)

    def test_all_proper_three_variable_cnf_subsets(self):
        universe = [tuple(v*s for v, s in enumerate(signs, 1))
                    for signs in product((-1, 1), repeat=3)]
        for mask in range(256):
            clauses = [c for j, c in enumerate(universe) if mask & (1 << j)]
            circuit = cnf_circuit(3, clauses)
            for bits in product((False, True), repeat=3):
                expected = all(any(bits[abs(lit)-1] == (lit > 0) for lit in c) for c in clauses)
                self.assertEqual(circuit.evaluate(bits)[circuit.output-1], expected)

    def test_complete_small_cnf_to_phase_chain(self):
        for n, clauses in [(1, []), (1, [()]), (1, [(1,)]), (1, [(1,), (-1,)]),
                           (2, [(1,), (2,)]), (2, [(-1, -2)]), (2, [(1,), (1,)])]:
            phase = circuit_phase(cnf_circuit(n, clauses))
            count = sum(all(any(bits[abs(lit)-1] == (lit > 0) for lit in c) for c in clauses)
                        for bits in product((False, True), repeat=n))
            self.assertEqual(exact_gap(phase['variables'], phase['terms']), phase['scale']*count)

    def test_constants_cancellation_and_large_quadratic_control(self):
        for n in (0, 1, 5):
            self.assertEqual(quadratic_gap(n, [])['gap'], 1 << n)
            self.assertEqual(quadratic_gap(n, [0])['gap'], -(1 << n))
            self.assertEqual(quadratic_gap(n, [0, 0])['gap'], 1 << n)
        self.assertEqual(quadratic_gap(1, [1, 1, 1])['gap'], 0)
        # Independent pairs factor into gaps of 2; there are also 20 free bits.
        pairs = [(1 << (2*j)) | (1 << (2*j+1)) for j in range(40)]
        control = quadratic_gap(100, pairs)
        self.assertEqual(control['gap'], 1 << 60)
        self.assertEqual(control['eliminated_pairs'], 40)
        self.assertEqual(quadratic_gap(100, [0, *pairs])['gap'], -(1 << 60))
        self.assertEqual(quadratic_gap(100, [1 << 99, *pairs])['gap'], 0)

    def test_cubic_counterexample_and_enumeration_budgets(self):
        self.assertEqual(exact_gap(3, [7]), 6)
        with self.assertRaises(ValueError):
            quadratic_gap(3, [7])
        # The same invalid coefficient replacement fails on the promised image,
        # not merely on an arbitrary cubic polynomial outside the SAT reduction.
        phase = circuit_phase(Circuit(2, (Gate('AND', (1, 2)),), 3))
        self.assertEqual(phase['terms'], [11, 12, 16, 20])
        self.assertEqual(truth_gap(5, phase['terms']), 4)
        self.assertEqual(2*truth_gap(3, [3, 5, 4]), 0)
        self.assertEqual(exact_gap(3, [7], assignment_limit=8), 6)
        for n, limit in ((0, 0), (3, 7), (10**6, 1)):
            with self.assertRaises(PhaseBudgetExceeded):
                exact_gap(n, [], assignment_limit=limit)

    def test_invalid_polynomial_and_cnf_inputs(self):
        for function in (exact_gap, quadratic_gap):
            for n, terms in [(-1, []), (True, []), (1, [2]), (1, [-1]), (1, [True])]:
                with self.assertRaises(ValueError):
                    function(n, terms)
        for budget in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                exact_gap(1, [], assignment_limit=budget)
        for n, clauses in [(0, []), (2, [(3,)]), (4, [(1, 2, 3, 4)]), (2, [(1, -1)])]:
            with self.assertRaises(ValueError):
                cnf_circuit(n, clauses)


if __name__ == '__main__':
    unittest.main()
