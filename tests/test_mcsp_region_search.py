from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product
import unittest

from experiments.mcsp_counterexample_search import semantic_catalog
from pnp_lab.mcsp_counterexample import witness_table
from pnp_lab.mcsp_region_search import depth_exclusion, search_regions, solve_samples


@lru_cache(None)
def literal_suffix_exists(values, target, width, remaining):
    """Independent literal suffix enumeration; retain duplicate wire values."""
    if target in values:
        return True
    if remaining == 0:
        return False
    mask = (1 << width) - 1
    outputs = [mask ^ a for a in values]
    for a, b in combinations_with_replacement(values, 2):
        outputs.extend((a & b, a | b))
    return any(literal_suffix_exists((*values, value), target, width, remaining - 1)
               for value in outputs)


class RegionSynthesisTests(unittest.TestCase):
    def test_all_two_input_partial_tables(self):
        for budget in range(3):
            feasible = semantic_catalog(2, budget)
            for partial in product((-1, 0, 1), repeat=4):
                examples = [(row, bit) for row, bit in enumerate(partial) if bit >= 0]
                exists = any(all(table >> row & 1 == bit for row, bit in examples)
                             for table in feasible)
                for cap in (0, 1, 128):
                    result = solve_samples(2, budget, examples, relaxation_limit=cap)
                    self.assertEqual(result['status'] == 'YES', exists)
                    if result['witness']:
                        table = witness_table(result['witness'])
                        self.assertLessEqual(len(result['witness']['gates']), budget)
                        self.assertTrue(all(table >> row & 1 == bit for row, bit in examples))

    def test_depth_exclusion_never_removes_a_literal_completion(self):
        for selected in range(1, 16):
            values = tuple(i for i in range(4) if selected >> i & 1)
            for target, remaining, cap in product(range(4), range(3), (0, 1, 128)):
                excluded = depth_exclusion(values, target, 2, remaining, cap, Counter())
                if excluded is True:
                    self.assertFalse(literal_suffix_exists(values, target, 2, remaining))

    def test_refinement_restores_distinguished_candidates(self):
        result = search_regions(2, 2, 14)  # OR: two inputs initially look equal to simpler choices.
        self.assertEqual(result['examples'], [[1, 1], [0, 0], [2, 1]])
        self.assertEqual(result['metrics']['synthesis_rounds'], 4)
        self.assertEqual(witness_table(result['witness']), 14)
        tables = [witness_table(r['witness']) for r in result['iterations']]
        self.assertEqual(tables, [0, 15, 10, 14])
        for iteration in result['iterations']:
            self.assertTrue(all(witness_table(iteration['witness']) >> row & 1 == bit
                                for row, bit in iteration['examples']))

    def test_root_region_excluded_without_child_generation(self):
        result = solve_samples(2, 2, [(row, 6 >> row & 1) for row in range(4)])
        self.assertEqual(result['status'], 'NO')
        self.assertEqual(result['metrics']['states_created'], 1)
        self.assertEqual(result['metrics']['transition_attempts'], 0)
        self.assertEqual(len(result['pruned_regions']), 1)
        cut = result['pruned_regions'][0]
        self.assertFalse(literal_suffix_exists(tuple(cut['available']), 6, 4, 2))
        self.assertEqual(cut['relax_gate_ops'], 104)

    def test_a_rejected_output_can_still_be_a_necessary_intermediate(self):
        for cap in (0, 1, 128):
            result = search_regions(2, 4, 6, relaxation_limit=cap)
            self.assertEqual(result['status'], 'YES')
            self.assertEqual(witness_table(result['witness']), 6)
            self.assertEqual(len(result['witness']['gates']), 4)

    def test_every_three_input_truth_table_at_budget_two(self):
        feasible = semantic_catalog(3, 2)
        for table in range(256):
            result = search_regions(3, 2, table)
            self.assertEqual(result['status'] == 'YES', table in feasible)
            if result['witness']:
                self.assertEqual(witness_table(result['witness']), table)
            self.assertLessEqual(result['metrics']['synthesis_rounds'], 9)
            self.assertEqual(len(result['examples']), len({row for row, _ in result['examples']}))

    def test_timeout_of_relaxation_is_not_an_impossibility_proof(self):
        stats = Counter()
        self.assertIsNone(depth_exclusion((0, 3, 5, 15), 6, 4, 4, 1, stats))
        self.assertEqual(stats['relax_unknown'], 1)
        result = search_regions(2, 4, 6, relaxation_limit=1)
        self.assertEqual(result['status'], 'YES')
        self.assertGreater(result['metrics']['relax_unknown'], 0)

    def test_invalid_inputs_and_zero_budget(self):
        with self.assertRaises(ValueError):
            solve_samples(2, 2, [(0, 0), (0, 1)])
        with self.assertRaises(ValueError):
            solve_samples(2, 2, [(4, 0)])
        with self.assertRaises(ValueError):
            search_regions(2, 2, 16)
        self.assertEqual(search_regions(2, 0, 0)['status'], 'YES')
        self.assertEqual(search_regions(2, 0, 6)['status'], 'NO')


if __name__ == '__main__':
    unittest.main()
