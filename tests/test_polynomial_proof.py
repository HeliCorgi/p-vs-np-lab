import copy
from itertools import product
import unittest

from pnp_lab.modular_barrier import line_fixture
from pnp_lab.polynomial_proof import (check_polynomial_proof, polynomial_refute,
                                     resolution_to_polynomial)
from pnp_lab.resolution_closure import resolution_refute


def holds(cs, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs)


class PolynomialProofTests(unittest.TestCase):
    def test_complete_two_variable_formulas_against_boolean_oracle(self):
        possible = [(), (1,), (-1,), (2,), (-2,)]
        possible += list(product((1, -1), (2, -2)))
        for selected in range(1 << len(possible)):
            cs = [c for i, c in enumerate(possible) if selected >> i & 1]
            sat = any(holds(cs, word) for word in range(4))
            answer = polynomial_refute(2, cs, width=2, max_rows=100, max_pairs=1000)
            self.assertEqual(answer['status'], 'UNKNOWN' if sat else 'UNSAT')
            if not sat:
                self.assertTrue(check_polynomial_proof(2, cs, answer['certificate']))
                self.assertLessEqual(answer['certificate']['degree'], 3)

    def test_nonlinear_core_exact_trace_degree_and_tampering(self):
        n, cs = line_fixture(0)
        cs = cs[:152]
        source = resolution_refute(n, cs, width=4)
        self.assertEqual(source['status'], 'UNSAT')
        answer = resolution_to_polynomial(n, cs, source['certificate'], max_degree=5)
        self.assertEqual(answer['status'], 'UNSAT')
        cert = answer['certificate']
        self.assertEqual(cert['degree'], 5)
        self.assertTrue(check_polynomial_proof(n, cs, cert, max_degree=5))
        self.assertFalse(check_polynomial_proof(n, cs, cert, max_degree=4))
        positive = [tuple(map(abs, c)) for c in cs]
        self.assertTrue(holds(positive, (1 << n)-1))
        self.assertFalse(check_polynomial_proof(n, positive, cert))
        for field, value in (('kind', 'made-up'), ('field', 3), ('field', True),
                             ('variables', n+1), ('degree', 4), ('degree', 6),
                             ('root', True), ('root', 0), ('nodes', [])):
            bad = copy.deepcopy(cert)
            bad[field] = value
            self.assertFalse(check_polynomial_proof(n, cs, bad), (field, value))
        for operation in ('input', 'add', 'multiply'):
            bad = copy.deepcopy(cert)
            node_index = next(i for i, node in enumerate(bad['nodes']) if node['op'] == operation)
            node = bad['nodes'][node_index]
            if operation == 'input':
                node['clause'] = len(cs)
            elif operation == 'add':
                node['left'] = node_index
            else:
                node['variable'] = n+1
            self.assertFalse(check_polynomial_proof(n, cs, bad), operation)
        for limits in ({'max_degree': 4}, {'max_nodes': 0}, {'max_monomials': 0}, {'max_work': 0}):
            capped = resolution_to_polynomial(n, cs, source['certificate'], **limits)
            self.assertEqual(capped['status'], 'UNKNOWN')
            self.assertIsNone(capped['certificate'])
            self.assertTrue(capped['stats']['budget_limited'])

    def test_raw_indices_empty_clause_and_sparse_large_names(self):
        n = 10**9
        cs = [(1, -1), (n,), (-n,)]
        source = dict(kind='boolean-resolution-v1', width=2, nodes=[
            dict(op='input', clause=1), dict(op='input', clause=2),
            dict(op='resolve', left=0, right=1, pivot=n)], root=2)
        answer = resolution_to_polynomial(n, cs, source)
        self.assertEqual(answer['status'], 'UNSAT')
        self.assertEqual(answer['certificate']['degree'], 1)
        self.assertTrue(check_polynomial_proof(n, cs, answer['certificate']))
        self.assertFalse(check_polynomial_proof(n, [(1, -1), (-n,), (-n,)], answer['certificate']))
        empty = polynomial_refute(0, [()], width=0)
        self.assertEqual((empty['status'], empty['certificate']['degree']), ('UNSAT', 0))
        self.assertTrue(check_polynomial_proof(0, [()], empty['certificate']))
        streamed = polynomial_refute(1, (c for c in ((1,), (-1,))))
        self.assertEqual(streamed['status'], 'UNSAT')
        self.assertTrue(check_polynomial_proof(1, [(1,), (-1,)], streamed['certificate']))
        with self.assertRaises(ValueError):
            resolution_to_polynomial(n, cs, dict(source, root=0))
        for limits in ({'max_degree': -1}, {'max_nodes': True}, {'max_monomials': -1}, {'max_work': 0.5}):
            with self.assertRaises(ValueError):
                polynomial_refute(1, [(1,), (-1,)], **limits)

    def test_source_validation_respects_tiny_budgets(self):
        cs = [(1,), (-1,)]
        source = dict(kind='boolean-resolution-v1', width=10**9, nodes=[
            dict(op='input', clause=0), dict(op='input', clause=1),
            dict(op='resolve', left=0, right=1, pivot=1)], root=2)
        # The source's declared ceiling may be loose. Charge actual clauses.
        answer = resolution_to_polynomial(1, cs, source, max_degree=1)
        self.assertEqual(answer['status'], 'UNSAT')
        self.assertEqual(answer['certificate']['degree'], 1)
        for limits in ({'max_nodes': 2}, {'max_degree': 0}, {'max_work': 1}):
            capped = resolution_to_polynomial(1, cs, source, **limits)
            self.assertEqual(capped['status'], 'UNKNOWN')
            self.assertIsNone(capped['certificate'])
            self.assertTrue(capped['stats']['budget_limited'])
            # Validation stops before generating any arithmetic proof nodes.
            self.assertEqual(capped['stats']['generated_nodes'], 0)
