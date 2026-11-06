"""Adversarial finite checks for the exact one-cover theorem, NOT a proof."""
import unittest

from experiments.exact_affine_one_cover import all_rref_bases, audit, q, subspace_vectors


class ExactAffineOneCoverTests(unittest.TestCase):
    def test_q_agrees_with_independent_coordinate_oracle(self):
        for m in (1, 2, 3):
            mask = (1 << m) - 1
            for z in range(1 << (2 * m)):
                x, y = z & mask, z >> m
                expected = sum(((x >> i) & 1) * ((y >> i) & 1)
                               for i in range(m)) % 2
                self.assertEqual(q(m, z), expected)

    def test_unique_rref_subspaces_and_gaussian_counts(self):
        # Independently known Gaussian binomial coefficients [n choose d]_2.
        for n, expected in ((2, [1, 3, 1]),
                            (4, [1, 15, 35, 15, 1]),
                            (6, [1, 63, 651, 1395, 651, 63, 1])):
            for d, count in enumerate(expected):
                directions = [subspace_vectors(basis)
                              for basis in all_rref_bases(n, d)]
                self.assertEqual(len(directions), count)
                self.assertEqual(len(set(directions)), count)

    def test_complete_coset_audit_and_optimal_partition(self):
        for m, points, positive_flats, total_cosets in (
            (1, 1, {0: 1}, 11),
            (2, 6, {0: 6, 1: 15}, 307),
            (3, 28, {0: 28, 1: 378, 2: 315}, 26387),
        ):
            r = audit(m)
            self.assertEqual(r['positive_points'], points)
            self.assertEqual(r['positive_cosets_by_dim'], positive_flats)
            self.assertEqual(sum(r['cosets_by_dim'].values()), total_cosets)
            self.assertEqual(r['largest_positive_flat_dim'], m - 1)
            self.assertEqual(r['exact_minimum_cover_from_proved_size_bound'], 2**m - 1)
            self.assertEqual(r['explicit_partition_charts'], 2**m - 1)

    def test_budget_is_not_silently_expanded(self):
        with self.assertRaises(ValueError):
            audit(4)
        with self.assertRaises(ValueError):
            audit(0)


if __name__ == '__main__':
    unittest.main()
