"""Truth-table Möbius inversion is independent of circuit polynomial expansion."""
from itertools import product
import random
import unittest

from pnp_lab.circuit_extensions import Circuit, Gate, inner_product
from pnp_lab.extension_degree import (
    ExpansionLimit, degree, evaluate, expand, gate_residuals,
    ordinary_product, reduction_circuit, squarefree)


def truth_table_anf(n, truth):
    coefficients = [int(truth(tuple(bool(mask >> i & 1) for i in range(n))))
                    for mask in range(1 << n)]
    for i in range(n):
        for mask in range(1 << n):
            if mask >> i & 1:
                coefficients[mask] ^= coefficients[mask ^ (1 << i)]
    return frozenset(tuple(i+1 for i in range(n) if mask >> i & 1)
                     for mask, coefficient in enumerate(coefficients) if coefficient)


class ExtensionDegreeTests(unittest.TestCase):
    def test_random_dag_coordinates_against_independent_mobius_transform(self):
        rng = random.Random(2701)
        for n in (1, 2, 3, 4):
            for _ in range(8):
                gates = []
                for j in range(8):
                    kind = rng.choice(('AND', 'XOR', 'NOT'))
                    gates.append(Gate(kind, tuple(rng.randrange(1, n+j+1)
                                                  for _ in range(1 if kind == 'NOT' else 2))))
                circuit = Circuit(n, tuple(gates), n+8)
                expansion = expand(circuit)
                for i, q in enumerate(expansion['coordinates']):
                    expected = truth_table_anf(n, lambda w: circuit.evaluate(w)[i])
                    self.assertEqual(q, expected)
                for residual in gate_residuals(circuit, expansion['coordinates']):
                    self.assertTrue(all(evaluate(residual, w) == 0
                                        for w in product((False, True), repeat=n)))

    def test_sharp_and_degree_and_ordinary_boolean_cost(self):
        for n in (1, 2, 3, 4, 8, 16, 32):
            for balanced in (False, True):
                circuit = reduction_circuit(n, 'AND', balanced=balanced)
                result = expand(circuit)
                q = result['coordinates'][circuit.output-1]
                self.assertEqual(q, frozenset({tuple(range(1, n+1))}))
                self.assertEqual(result['coordinate_degree'], n)
                self.assertEqual(len(circuit.gates), n-1)
                residual = ordinary_product(q, q) ^ q
                self.assertEqual(degree(residual), 2*n)
                self.assertEqual(squarefree(residual), frozenset())
                if balanced:
                    self.assertEqual(result['multiplication_depth'], (n-1).bit_length())

    def test_or_size_blowup_and_parity_control(self):
        for n in range(1, 9):
            for operation in ('OR', 'XOR'):
                circuit = reduction_circuit(n, operation, balanced=True)
                result = expand(circuit)
                expected = truth_table_anf(n, lambda w: any(w) if operation == 'OR'
                                          else sum(w) % 2)
                self.assertEqual(result['coordinates'][circuit.output-1], expected)
                self.assertEqual(result['output_terms'], 2**n-1 if operation == 'OR' else n)
                self.assertEqual(result['output_degree'], n if operation == 'OR' else 1)
        self.assertEqual(expand(inner_product(32))['coordinate_degree'], 2)

    def test_boolean_reduction_is_not_an_ordinary_polynomial_identity(self):
        circuit = Circuit(1, (Gate('AND', (1, 1)),), 2)
        coordinates = expand(circuit)['coordinates']
        self.assertEqual(gate_residuals(circuit, coordinates),
                         (frozenset({(1,), (1, 1)}),))
        self.assertNotEqual(gate_residuals(circuit, coordinates)[0], frozenset())

    def test_resource_exhaustion_is_explicit(self):
        circuit = reduction_circuit(12, 'OR')
        with self.assertRaises(ExpansionLimit):
            expand(circuit, max_terms=100)
        with self.assertRaises(ExpansionLimit):
            expand(circuit, max_work=100)
        with self.assertRaises(ValueError):
            expand(circuit, max_work=-1)


if __name__ == '__main__':
    unittest.main()
