import copy
import unittest

from pnp_lab.correlation import check_correlation_report, solve_correlations


class CorrelationEntryTests(unittest.TestCase):
    def test_each_representation_replays_against_original_input(self):
        cs = [(1,), (-1, 2), (-2,)]
        for method in ('resolution', 'relations', 'polynomial'):
            out = solve_correlations(2, (c for c in cs), method=method)
            self.assertEqual(out['status'], 'UNSAT')
            self.assertEqual(check_correlation_report(2, cs, out), 'original CNF is UNSAT')
            self.assertIsNone(check_correlation_report(2, [(1,), (1, 2), (2,)], out))
        with self.assertRaises(ValueError):
            solve_correlations(0, [], method='invented')

    def test_relaxation_and_bounded_closure_are_not_global_models(self):
        cs = [(1, 2, 3)]
        out = solve_correlations(3, cs, method='marginals')
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertIn('original CNF is undecided', check_correlation_report(3, cs, out))
        for status in ('SAT', 'UNSAT'):
            forged = copy.deepcopy(out)
            forged['status'] = status
            self.assertIsNone(check_correlation_report(3, cs, forged))
        closure = solve_correlations(3, cs, method='resolution', width=3)
        self.assertIn('width <= 3', check_correlation_report(3, cs, closure))
        capped = solve_correlations(3, cs, max_rows=0)
        self.assertIsNone(check_correlation_report(3, cs, capped))
