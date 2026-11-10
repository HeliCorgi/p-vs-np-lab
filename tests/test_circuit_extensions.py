"""Independent truth-table and proof-tampering controls for extensions."""
import copy
from itertools import product
import unittest

from pnp_lab.circuit_extensions import (
    Circuit, Gate, duplicate_miter, inner_product, refute_duplicate, tseitin)
from pnp_lab.resolution_closure import check_resolution


def satisfies(clauses, values):
    return all(any(values[abs(l)-1] == (l > 0) for l in c) for c in clauses)


class CircuitExtensionTests(unittest.TestCase):
    def test_all_gate_truth_tables_and_unique_extension(self):
        for kind, arity, truth in (
            ('AND', 2, lambda a: all(a)),
            ('XOR', 2, lambda a: sum(a) == 1),
            ('NOT', 1, lambda a: not a[0]),
        ):
            circuit = Circuit(arity, (Gate(kind, tuple(range(1, arity+1))),), arity+1)
            for original in product((False, True), repeat=arity):
                for required in (False, True):
                    _, cs = tseitin(circuit, required)
                    extensions = [z for z in (False, True) if satisfies(cs, (*original, z))]
                    self.assertEqual(extensions, [required] if truth(original) == required else [])

    def test_inner_product_projection_counts_every_auxiliary_assignment(self):
        for m in (1, 2, 3):
            circuit = inner_product(m)
            for required in (False, True):
                n, cs = tseitin(circuit, required)
                self.assertEqual(n, 4*m-1)
                self.assertEqual(len(cs), 7*m-3)
                for original in product((False, True), repeat=2*m):
                    expected = sum(original[i] * original[m+i] for i in range(m)) % 2
                    extensions = [aux for aux in product((False, True), repeat=2*m-1)
                                  if satisfies(cs, original+aux)]
                    self.assertEqual(len(extensions), int(expected == required))
                    if extensions:
                        self.assertEqual(circuit.evaluate(original), original+extensions[0])

    def test_small_miters_and_equal_output_sat_control(self):
        for m in (1, 2):
            circuit = inner_product(m)
            n, cs, _ = duplicate_miter(circuit)
            self.assertFalse(any(satisfies(cs, w) for w in product((False, True), repeat=n)))
            same_output = (*cs[:-1], (-cs[-1][0],))
            self.assertTrue(any(satisfies(same_output, w)
                                for w in product((False, True), repeat=n)))
            cert = refute_duplicate(circuit)['certificate']
            self.assertFalse(check_resolution(n, same_output, cert))

    def test_linear_certificates_checked_on_original_cnf(self):
        for m in (1, 2, 3, 8, 64, 1024):
            r = refute_duplicate(inner_product(m))
            self.assertEqual(r['variables'], 6*m-2)
            self.assertEqual(len(r['clauses']), 14*m-6)
            self.assertEqual(r['stats']['proof_nodes'], 32*m-18)
            self.assertEqual(r['stats']['proof_width'], 3)
            self.assertLessEqual(r['stats']['max_local_variables'], 6)
            self.assertTrue(check_resolution(r['variables'], r['clauses'], r['certificate']))

    def test_fanout_repeated_inputs_negation_and_input_output(self):
        for circuit in (
            Circuit(1, (), 1),
            Circuit(1, (Gate('AND', (1, 1)), Gate('NOT', (2,)), Gate('XOR', (2, 3))), 4),
            Circuit(2, (Gate('XOR', (1, 1)), Gate('AND', (3, 3))), 4),
            Circuit(2, (Gate('NOT', (1,)),), 2),
        ):
            r = refute_duplicate(circuit)
            self.assertTrue(check_resolution(r['variables'], r['clauses'], r['certificate']))

    def test_rejects_tampered_proofs_and_missing_gate_constraint(self):
        r = refute_duplicate(inner_product(3))
        cert = copy.deepcopy(r['certificate'])
        cert['nodes'][-1]['pivot'] = r['variables'] + 1
        self.assertFalse(check_resolution(r['variables'], r['clauses'], cert))
        cert = copy.deepcopy(r['certificate'])
        cert['nodes'][-1]['left'] = cert['root']
        self.assertFalse(check_resolution(r['variables'], r['clauses'], cert))
        cs = list(r['clauses'])
        cs[-1] = (1, -1)
        self.assertFalse(check_resolution(r['variables'], cs, r['certificate']))
        small = refute_duplicate(inner_product(1))
        cs = list(small['clauses'])
        cs[0] = (1, -1)  # Remove an essential AND constraint, preserving indices.
        self.assertTrue(any(satisfies(cs, w) for w in product((False, True), repeat=4)))
        self.assertFalse(check_resolution(4, cs, small['certificate']))

    def test_invalid_dags(self):
        for gate in (Gate('AND', (1, 3)), Gate('OR', (1, 2)), Gate('NOT', (0,))):
            with self.assertRaises(ValueError):
                Circuit(2, (gate,), 3)
        with self.assertRaises(ValueError):
            inner_product(0)
        with self.assertRaises(ValueError):
            tseitin(inner_product(1), 1)


if __name__ == '__main__':
    unittest.main()
