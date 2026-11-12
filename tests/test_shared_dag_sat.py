import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

from pnp_lab.circuit_extensions import Circuit, Gate
from pnp_lab.extension_degree import expand, ZERO
from pnp_lab.shared_dag_sat import (
    SharedDAG, complement, distributivity_miter, solve_circuit, solve_cnf,
)


class SharedDAGSATTests(unittest.TestCase):
    def test_all_two_variable_cnf_sets_against_exhaustive_search(self):
        possible = [tuple(v * sign for v, sign in enumerate(signs, 1) if sign)
                    for signs in itertools.product((-1, 0, 1), repeat=2)]
        for mask in range(1 << len(possible)):
            clauses = [c for i, c in enumerate(possible) if mask >> i & 1]
            expected = any(all(any(values[abs(x) - 1] == (x > 0) for x in c)
                               for c in clauses)
                           for values in itertools.product((False, True), repeat=2))
            result = solve_cnf(clauses)
            self.assertEqual(result['status'], 'SAT' if expected else 'UNSAT')

    def test_random_circuits_and_orders_against_original_truth_tables(self):
        rng = random.Random(2801)
        for trial in range(64):
            n = 1 + trial % 5
            gates = []
            for _ in range(14):
                kind = rng.choice(('AND', 'XOR', 'NOT'))
                wires = tuple(rng.randint(1, n + len(gates))
                              for _ in range(1 if kind == 'NOT' else 2))
                gates.append(Gate(kind, wires))
            circuit = Circuit(n, tuple(gates), n + len(gates))
            outputs = {circuit.evaluate(values)[circuit.output - 1]
                       for values in itertools.product((False, True), repeat=n)}
            shuffled = list(range(1, n + 1))
            rng.shuffle(shuffled)
            for value in (False, True):
                for order in (None, tuple(reversed(range(1, n + 1))), shuffled):
                    result = solve_circuit(circuit, value=value, order=order)
                    self.assertEqual(result['status'], 'SAT' if value in outputs else 'UNSAT')
                    if result['status'] == 'SAT':
                        assignment = result['assignment']
                        self.assertEqual(circuit.evaluate(tuple(assignment[i]
                            for i in range(1, n + 1)))[circuit.output - 1], value)

    def test_normalization_complements_and_all_term_factoring(self):
        manager = SharedDAG()
        a, b, c = (manager.variable(i) for i in range(1, 4))
        self.assertEqual(manager.conjunction([a, a, 1]), a)
        self.assertEqual(manager.conjunction([a, complement(a)]), 0)
        self.assertEqual(manager.exclusive_or([a, complement(a)]), 1)
        left = manager.exclusive_or([manager.conjunction([a, b]),
                                     manager.conjunction([a, c])])
        right = manager.conjunction([a, manager.exclusive_or([b, c])])
        self.assertEqual(left, right)
        self.assertEqual(manager.exclusive_or([left, right]), 0)

    def test_miter_is_zero_by_independent_polynomial_expansion(self):
        for k in (1, 2, 3, 6, 12):
            for selectors in (1, 2):
                circuit = distributivity_miter(k, selectors=selectors)
                self.assertEqual(expand(circuit)['coordinates'][circuit.output - 1], ZERO)
                if k <= 3:
                    for values in itertools.product((False, True), repeat=circuit.inputs):
                        self.assertFalse(circuit.evaluate(values)[circuit.output - 1])

    def test_distinct_residual_prefixes_and_actual_unsat_decision_states(self):
        for k in range(2, 10):
            circuit = distributivity_miter(k)
            manager = SharedDAG()
            roots = {manager.from_circuit(circuit)}
            for v in range(1, k - 1):
                roots = {manager.cofactor(root, v, bit)
                         for root in roots for bit in (False, True)}
            self.assertEqual(len(roots), 2 ** (k - 2))
            self.assertFalse(roots & {0, 1})
            result = solve_circuit(circuit)
            self.assertEqual(result['status'], 'UNSAT')
            self.assertEqual(result['stats']['states_by_variable'][str(k - 1)], 2 ** (k - 2))
            self.assertGreaterEqual(result['stats']['expanded_states'], 2 ** (k - 2))

    def test_selector_first_and_single_selector_controls(self):
        for k in (2, 4, 8, 12):
            order = (k + 1, k + 2, *range(1, k + 1), *range(k + 3, 2 * k + 3))
            result = solve_circuit(distributivity_miter(k), order=order)
            self.assertEqual(result['status'], 'UNSAT')
            self.assertEqual(result['stats']['expanded_states'], 2)
            result = solve_circuit(distributivity_miter(k, selectors=1))
            self.assertEqual(result['status'], 'UNSAT')
            self.assertEqual(result['stats']['expanded_states'], 0)

    def test_exhausted_budgets_are_unknown(self):
        circuit = distributivity_miter(4)
        for caps in ({'max_states': 0}, {'max_nodes': 0}, {'max_work': 0},
                     {'max_states': 5}):
            result = solve_circuit(circuit, **caps)
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertIsNone(result['assignment'])
            self.assertTrue(result['reason'])
        self.assertEqual(solve_cnf([], max_states=0)['status'], 'SAT')
        self.assertEqual(solve_cnf([[]], max_states=0)['status'], 'UNSAT')

    def test_sparse_labels_tautologies_and_invalid_arguments(self):
        result = solve_cnf([[1000001, -1000001], [-3]], order=(1000001, 3))
        self.assertEqual(result['status'], 'SAT')
        self.assertFalse(result['assignment'][3])
        for clauses in ([[0]], [[True]], [['x']]):
            with self.assertRaises(ValueError):
                solve_cnf(clauses)
        for order in ((1, 1), (), (2,), (True,)):
            with self.assertRaises(ValueError):
                solve_cnf([[1]], order=order)
        for cap in ('max_nodes', 'max_work', 'max_states'):
            for value in (-1, True, 1.5):
                with self.assertRaises(ValueError):
                    solve_cnf([[1]], **{cap: value})

    def test_search_deeper_than_python_recursion_limit(self):
        n = 1050
        result = solve_cnf([[v] for v in range(1, n + 1)], max_work=None)
        self.assertEqual(result['status'], 'SAT')
        self.assertEqual(result['stats']['expanded_states'], n)
        self.assertTrue(all(result['assignment'].values()))

    def test_cli_sat_unsat_and_unknown(self):
        script = Path(__file__).resolve().parents[1] / 'scripts' / 'solve_shared_dag.py'
        for clauses, options, status, code in (
            ([[1, 2], [-1, 2]], [], 'SAT', 10),
            ([[1], [-1]], [], 'UNSAT', 20),
            ([[1, 2]], ['--max-states', '0'], 'UNKNOWN', 0),
        ):
            completed = subprocess.run([sys.executable, str(script), '-', *options],
                                       input=json.dumps({'clauses': clauses}),
                                       text=True, capture_output=True)
            self.assertEqual(completed.returncode, code, completed.stderr)
            self.assertEqual(json.loads(completed.stdout)['status'], status)


if __name__ == '__main__':
    unittest.main()
