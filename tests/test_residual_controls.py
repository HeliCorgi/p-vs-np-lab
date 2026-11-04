from itertools import product
import unittest

from pnp_lab.residual_controls import (comparator_cnf, majority, modular_collision,
                                       predicted_residual_count, residual_cnf, satisfies)


class ResidualControlTests(unittest.TestCase):
    def test_actual_gate_semantics_and_unique_extension(self):
        k = 3
        clauses = comparator_cnf(k)
        for t, u in product(range(1 << k), repeat=2):
            states = [q for q in range(1 << k) if satisfies(clauses, t | u << k | q << (2*k))]
            correct = sum(int((u % (2 << i)) <= (t % (2 << i))) << i for i in range(k))
            self.assertEqual(states, [correct] if u <= t else [])

    def test_prefix_anchor_and_deletion_scope(self):
        k, d = 4, 3
        count, anchor = residual_cnf(k, d, 0)
        points = {x for x in range(1 << count) if satisfies(anchor, x)}
        self.assertEqual(len(points), 3)
        counts = []
        for p in range(1, 1 << d):
            n, other = residual_cnf(k, d, p)
            self.assertEqual(n, count)
            good = {x for x in range(1 << count) if satisfies(other, x)}
            self.assertTrue(points <= good)
            counts.append(len(good | points))
            self.assertEqual(counts[-1], predicted_residual_count(k, d, p))
        self.assertEqual(counts, [7, 11, 15, 19, 23, 27, 31])

    def test_modular_false_collision(self):
        for m in (1, 7, 16, 19):
            n, a, sat, unsat = modular_collision(m)
            def points(h):
                return {x for x in range(1 << n) if satisfies(h, x) or satisfies(a, x)}
            pos, neg = points(sat), points(unsat)
            self.assertTrue(pos)
            self.assertFalse(neg)
            self.assertEqual((len(pos), len(neg)), (m, 0))
            self.assertEqual(len(pos) % m, len(neg) % m)
        for m in (-1, 0, True):
            with self.assertRaises(ValueError):
                modular_collision(m)

    def test_existential_two_cnf_majority_and_tight_block(self):
        # Three binary clauses force hidden h=1-x plus one forbidden pair.
        cs = ((1, 4), (-1, -4), (1, 2))
        points = {w & 7 for w in range(16) if satisfies(cs, w)}
        self.assertEqual(len(points), 6)
        self.assertNotIn(0, points)
        self.assertEqual(len({1, 2, 4} & points), 2)
        self.assertTrue(all(majority(a, b, c) in points for a, b, c in product(points, repeat=3)))

    def test_malformed_prefix_rejected(self):
        for v in ((0, 0, 0), (2, 3, 0), (2, 1, 2), (2, -1, 0), (2, 1, False)):
            with self.assertRaises(ValueError):
                residual_cnf(*v)
