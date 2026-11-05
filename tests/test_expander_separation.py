from fractions import Fraction
import unittest

from experiments.expander_separation import finite_support_audit, parameter_audit, run


class ExpanderSeparationTests(unittest.TestCase):
    def test_connected_support_is_stronger_than_raw_clause_containment(self):
        out = finite_support_audit(6, [(1, 2, 3), (3, 4, 5), (1, 5, 6)], 12)
        self.assertTrue(out['strict_half_boundary_expansion'])
        self.assertIn([2, 4, 6], out['raw_clause_only_false_negatives'])
        self.assertEqual(out['good_monomials_by_degree'][3], 16)

    def test_exact_harris_product_and_invalid_expansion_control(self):
        for p in (Fraction(1, 8), Fraction(1, 2), Fraction(3, 4)):
            out = finite_support_audit(6, [(1, 2, 3), (4, 5, 6)], 12, p)
            self.assertEqual(Fraction(out['bernoulli_probability']), (1-p**3)**2)
            self.assertEqual(out['bernoulli_probability'], out['decreasing_event_product'])
        result = run()
        self.assertTrue(result['all_checks_passed'])
        self.assertFalse(result['cases'][2]['strict_half_boundary_expansion'])
        self.assertEqual(result['summary']['exhaustive_variable_subsets'], 192)

    def test_extreme_degree_interval_endpoints_are_exact_rationals(self):
        out = parameter_audit(10**60)
        self.assertTrue(out['all_rational_budget_checks_passed'])
        self.assertFalse(out['cnf_constructed'])
        self.assertFalse(out['specific_n_existence_certified'])
        self.assertGreater(Fraction(out['distinct_flat_bound_exponent_before_factor_one_quarter']), 1)
