from itertools import product
import unittest

from experiments.mcsp_counterexample_search import semantic_catalog
from experiments.mcsp_fixed_constraints import reference_model, satisfies_encoding
from pnp_lab.mcsp_counterexample import witness_table
from pnp_lab.mcsp_fixed_constraints import FixedCircuitSpace, search_fixed


class FixedCircuitSpaceTests(unittest.TestCase):
    def test_all_partial_two_input_tables(self):
        feasible = semantic_catalog(2, 2)
        for partial in product((-1, 0, 1), repeat=4):
            space = FixedCircuitSpace(2, 2)
            samples = [(row, bit) for row, bit in enumerate(partial) if bit >= 0]
            for row, bit in samples:
                space.add_example(row, bit)
            result = space.extract(max_work=None)
            possible = any(all(table >> row & 1 == bit for row, bit in samples) for table in feasible)
            self.assertEqual(result['status'] == 'YES', possible)
            if result['witness']:
                table = witness_table(result['witness'])
                self.assertTrue(all(table >> row & 1 == bit for row, bit in samples))

    def test_fixed_shape_and_monotone_updates(self):
        space = FixedCircuitSpace(3, 3)
        formula, shape = space.clauses, space.shape
        for row in range(8):
            previous = tuple(space.root)
            space.add_example(row, 128 >> row & 1)
            self.assertIs(space.clauses, formula)
            self.assertEqual(space.shape, shape)
            self.assertTrue(all(not old or old == new for old, new in zip(previous, space.root)))
        self.assertLessEqual(space.update_meter.stats['assigned_variables'], space.variables)
        before = tuple(space.root), tuple(space.root_trail)
        result = space.extract(max_work=None)
        self.assertEqual(witness_table(result['witness']), 128)
        self.assertEqual(before, (tuple(space.root), tuple(space.root_trail)))

    def test_refinement_all_two_input_tables(self):
        feasible = semantic_catalog(2, 2)
        for table in range(16):
            result = search_fixed(2, 2, table, max_work_per_extract=None)
            self.assertEqual(result['status'] == 'YES', table in feasible)
            self.assertTrue(result['shape_unchanged'])
            if result['witness']:
                self.assertEqual(witness_table(result['witness']), table)

    def test_unused_slots_do_not_require_branching(self):
        decisions = []
        for budget in (3, 6):
            space = FixedCircuitSpace(3, budget)
            for row in range(8):
                space.add_example(row, 128 >> row & 1)
            result = space.extract(max_work=50_000)
            self.assertEqual(result['status'], 'YES')
            self.assertEqual(witness_table(result['witness']), 128)
            decisions.append(result['metrics']['decisions'])
        self.assertEqual(decisions[0], decisions[1])

    def test_cap_preserves_root_and_is_not_no(self):
        space = FixedCircuitSpace(2, 2)
        space.add_example(0, 1)
        before = tuple(space.root), tuple(space.root_trail)
        result = space.extract(max_work=0)
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertEqual(before, (tuple(space.root), tuple(space.root_trail)))
        self.assertEqual(space.extract(max_work=None)['status'], 'YES')

    def test_duplicate_and_conflicting_evidence(self):
        space = FixedCircuitSpace(2, 2)
        space.add_example(1, 1)
        trail = tuple(space.root_trail)
        space.add_example(1, 1)
        self.assertEqual(tuple(space.root_trail), trail)
        space.add_example(1, 0)
        self.assertEqual(space.extract()['status'], 'NO')

    def test_encoding_rejects_bad_selectors_and_output(self):
        space = FixedCircuitSpace(2, 2)
        circuit = {'n': 2, 'gates': [['AND', [2, 3]]], 'output': 4}
        model = reference_model(space, circuit)
        self.assertTrue(satisfies_encoding(space, model))
        for variable in space.outputs:
            changed = list(model)
            changed[variable] *= -1
            self.assertFalse(satisfies_encoding(space, changed))
        changed = list(model)
        changed[space.output_choices[0]] = 1
        self.assertFalse(satisfies_encoding(space, changed))
        self.assertEqual(witness_table(space.decode(model)), 8)

    def test_zero_budget_and_validation(self):
        self.assertEqual(search_fixed(2, 0, 10)['status'], 'YES')
        self.assertEqual(search_fixed(2, 0, 6)['status'], 'NO')
        with self.assertRaises(ValueError):
            FixedCircuitSpace(0, 1)
        with self.assertRaises(ValueError):
            search_fixed(2, 2, 16)
        with self.assertRaises(ValueError):
            FixedCircuitSpace(2, 2).add_example(4, 0)


if __name__ == '__main__':
    unittest.main()
