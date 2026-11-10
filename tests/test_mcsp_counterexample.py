import unittest

from experiments.mcsp_counterexample_search import semantic_catalog
from pnp_lab.mcsp_counterexample import build_catalog, search, search_lazy, stream_catalog, witness_table


class CounterexampleSynthesisTests(unittest.TestCase):
    def test_complete_catalogue_against_independent_semantics(self):
        for n, budget in ((1, 0), (1, 1), (2, 2), (2, 4), (3, 2)):
            catalog = build_catalog(n, budget)
            actual = {witness_table(catalog.witness(root)) for root in range(len(catalog.nodes))}
            self.assertEqual(actual, semantic_catalog(n, budget))
            self.assertFalse(catalog.construction['uses_semantic_deduplication'])
            self.assertFalse(catalog.construction['uses_target_table'])

    def test_all_two_input_tables_and_sound_no(self):
        catalog = build_catalog(2, 2)
        for table in range(16):
            results = [search(catalog, table, mode) for mode in ('fresh', 'samples', 'samples_and_gates')]
            self.assertEqual(len({r['root'] for r in results}), 1)
            for result in results:
                self.assertEqual(result['status'], 'NO' if table in (6, 9) else 'YES')
                if result['witness'] is not None:
                    self.assertEqual(witness_table(result['witness']), table)
            self.assertEqual(results[1]['counterexample_rows'], results[2]['counterexample_rows'])
            self.assertLessEqual(results[2]['metrics']['gate_evaluations'],
                                 results[1]['metrics']['gate_evaluations'])

    def test_cache_and_distinct_counterexample_bounds(self):
        catalog = build_catalog(3, 2)
        for table in range(256):
            result = search(catalog, table)
            metrics = result['metrics']
            self.assertEqual(len(result['counterexample_rows']), len(set(result['counterexample_rows'])))
            self.assertLessEqual(len(result['counterexample_rows']), 8)
            self.assertLessEqual(metrics['gate_evaluations'], 8 * catalog.gate_count)
            self.assertLessEqual(metrics['row_root_checks'], 8 * metrics['candidate_visits'])
            self.assertLessEqual(metrics['peak_value_cache'], 8 * len(catalog.nodes))

    def test_export_preserves_internal_sharing(self):
        catalog = build_catalog(3, 3)
        lookup = {node: i for i, node in enumerate(catalog.nodes)}
        a = lookup[('AND', 2, 3)]
        b = lookup[('AND', 4, a)]
        root = lookup[('OR', a, b)]
        witness = catalog.witness(root)
        self.assertEqual(len(witness['gates']), 3)
        self.assertEqual(witness_table(witness), 192)

    def test_validation_rejects_malformed_witness(self):
        with self.assertRaises(ValueError):
            witness_table({'n': 2, 'gates': [['AND', [2, 9]]], 'output': 4})
        with self.assertRaises(ValueError):
            search(build_catalog(2, 0), 16)

    def test_lazy_generation_and_incomplete_no_are_distinct(self):
        complete = build_catalog(2, 2)
        for table in range(16):
            catalog, result = search_lazy(2, 2, table)
            self.assertEqual(result, search(complete, table))
            self.assertLessEqual(catalog.construction['transition_attempts'],
                                 complete.construction['transition_attempts'])
            if result['status'] == 'NO':
                self.assertTrue(catalog.construction['complete'])
        catalog, result = search_lazy(3, 3, 0)
        self.assertEqual(result['status'], 'YES')
        self.assertEqual(catalog.construction['transition_attempts'], 0)
        self.assertFalse(catalog.construction['complete'])
        partial, roots = stream_catalog(2, 2)
        with self.assertRaises(ValueError):
            search(partial, 6)  # Only the base nodes exist; this cannot prove NO.
        roots.close()
        with self.assertRaises(ValueError):
            search(complete, 6, roots=iter(range(4)))
        with self.assertRaises(ValueError):
            search(complete, 6, roots=iter((1, 0)))


if __name__ == '__main__':
    unittest.main()
