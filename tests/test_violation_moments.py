from itertools import combinations, product
from math import comb
import random
import unittest

from experiments.violation_moments import (AuditBudgetExceeded, binomial_moments,
    bonferroni_bounds, cubic_cnf, power_moments, prism_edges,
    subset_binomial_moments, violation_histogram, zero_mass)
from pnp_lab.sat_scaling import check_row_contradiction, gaussian, recognize_xor, satisfies


def reference_histogram(n, clauses):
    counts = [0] * (len(clauses) + 1)
    for bits in product((False, True), repeat=n):
        violations = sum(not any(bits[abs(lit) - 1] == (lit > 0) for lit in clause)
                         for clause in clauses)
        counts[violations] += 1
    return counts


class ViolationMomentTests(unittest.TestCase):
    def check_formula(self, n, clauses):
        hist = reference_histogram(n, clauses)
        self.assertEqual(violation_histogram(n, clauses), hist)
        moments = subset_binomial_moments(n, clauses, len(clauses))['moments']
        self.assertEqual(moments, binomial_moments(hist, len(clauses)))
        self.assertEqual(zero_mass(moments, maximum_violations=len(clauses)), hist[0])
        for r in range(len(clauses) + 1):
            lower, upper = bonferroni_bounds(moments[:r + 1])
            self.assertLessEqual(lower, hist[0])
            self.assertLessEqual(hist[0], upper)

    def test_all_three_variable_proper_clause_subsets(self):
        clauses = list(product((1, -1), (2, -2), (3, -3)))
        for mask in range(256):
            self.check_formula(3, [c for i, c in enumerate(clauses) if mask >> i & 1])

    def test_seeded_mixed_width_formulas_and_duplicate_positions(self):
        rng = random.Random(90117)
        for n in range(6):
            for _ in range(15):
                clauses = []
                for _ in range(rng.randrange(8)):
                    vs = rng.sample(range(1, n + 1), rng.randrange(min(n, 3) + 1))
                    clauses.append(tuple(v if rng.randrange(2) else -v for v in vs))
                self.check_formula(n, clauses)
        self.check_formula(2, [(1,), (1,), (-1, 2), ()])

    def test_k4_opposite_status_with_identical_first_three_moments(self):
        edges = tuple(combinations(range(4), 2))
        formulas = [cubic_cnf(4, edges, (b, 0, 0, 0)) for b in (0, 1)]
        hist = [reference_histogram(6, f) for f in formulas]
        self.assertEqual([h[0] for h in hist], [8, 0])
        self.assertEqual([power_moments(h, 3) for h in hist], [[64, 128, 320, 896]] * 2)
        self.assertEqual([power_moments(h, 4)[4] for h in hist], [2816, 2624])
        for f, h in zip(formulas, hist):
            self.assertEqual(subset_binomial_moments(6, f, 4)['moments'], binomial_moments(h, 4))

    def test_prism_distribution_and_gaussian_controls_on_original_clauses(self):
        for r in (3, 4):
            edges, q, n = prism_edges(r), 2*r, 3*r
            for b in (0, 1):
                clauses = cubic_cnf(q, edges, (b,) + (0,)*(q-1))
                hist = reference_histogram(n, clauses)
                self.assertEqual(hist, [2**(n-q+1) * comb(q, j) if j <= q and j % 2 == b else 0
                                       for j in range(4*q + 1)])
                self.assertEqual(binomial_moments(hist, q-1),
                                 [comb(q, t)*2**(n-t) for t in range(q)])
                equations = recognize_xor(n, clauses)
                answer = gaussian(n, equations)
                if b:
                    self.assertEqual(answer['status'], 'UNSAT')
                    self.assertTrue(check_row_contradiction(equations, answer['contradiction']))
                else:
                    self.assertEqual(answer['status'], 'SAT')
                    self.assertTrue(satisfies(clauses, answer['witness']))

    def test_empty_inputs_unused_variables_and_zeroth_moment(self):
        for n in (0, 1, 5):
            self.check_formula(n, [])
            self.check_formula(n, [()])
        self.assertEqual(power_moments([8], 0), [8])
        self.assertEqual(binomial_moments([8], 4), [8, 0, 0, 0, 0])

    def test_enumeration_budgets_raise_without_producing_a_decision(self):
        with self.assertRaises(AuditBudgetExceeded):
            violation_histogram(10, [(1,)], assignment_limit=1000)
        self.assertEqual(violation_histogram(2, [(1,)], assignment_limit=4), [2, 2])
        with self.assertRaises(AuditBudgetExceeded):
            subset_binomial_moments(3, [(1,), (2,), (3,)], 2, subset_limit=6)
        self.assertEqual(subset_binomial_moments(3, [(1,), (2,), (3,)], 2,
                                                subset_limit=7)['subsets_examined'], 7)

    def test_bad_inputs_and_incomplete_inversion_rejected(self):
        for n, clauses in ((-1, []), (1, [(0,)]), (1, [(2,)]), (1, [(1, -1)]),
                           (4, [(1, 2, 3, 4)])):
            with self.assertRaises(ValueError):
                violation_histogram(n, clauses)
        with self.assertRaises(ValueError):
            zero_mass([8, 3], maximum_violations=3)
        with self.assertRaises(ValueError):
            subset_binomial_moments(1, [(1,)], 2)
        for hist in ([], [-1], [True]):
            with self.assertRaises(ValueError):
                binomial_moments(hist, 1)
        with self.assertRaises(ValueError):
            prism_edges(2)
        with self.assertRaises(ValueError):
            cubic_cnf(4, ((0, 1), (1, 2)), (0,)*4)
        disconnected = tuple(combinations(range(4), 2)) + tuple(combinations(range(4, 8), 2))
        with self.assertRaises(ValueError):
            cubic_cnf(8, disconnected, (0,)*8)


if __name__ == '__main__':
    unittest.main()
