"""Check the 3-CNF bridge against original, independent Boolean semantics."""

import itertools
import random
import unittest

from pnp_lab.reductions import three_cnf_to_two_cnf_xor


def raw_cnf(clauses, values):
    return all(any(values[abs(literal) - 1] == int(literal > 0) for literal in clause)
               for clause in clauses)


class ThreeSatBridgeTests(unittest.TestCase):
    def test_every_local_input_and_auxiliary_assignment(self):
        reduction = three_cnf_to_two_cnf_xor(("a", "b", "c"), ((1, 2, 3),))
        for source in itertools.product((0, 1), repeat=3):
            count = 0
            for helpers in itertools.product((0, 1), repeat=3):
                full = source + helpers
                if sum(helpers) % 2 == 0 and raw_cnf(reduction.cnf, full):
                    count += 1
            true_occurrences = sum(source)
            self.assertEqual(count, 0 if true_occurrences == 0 else 1 << (true_occurrences - 1))

    def test_signed_clauses_and_shared_variables_against_full_projection(self):
        rng = random.Random(471329)
        for _ in range(24):
            clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randrange(1, 4) for _ in range(3))
                            for _ in range(2))
            reduction = three_cnf_to_two_cnf_xor(("a", "b", "c"), clauses)
            observed = set()
            for full in itertools.product((0, 1), repeat=9):
                if raw_cnf(reduction.cnf, full) and all(sum(full[j] for j in triple) % 2 == 0
                                                       for triple in reduction.auxiliary_triples):
                    observed.add(full[:3])
            expected = {v for v in itertools.product((0, 1), repeat=3) if raw_cnf(clauses, v)}
            self.assertEqual(observed, expected)
            for values in expected:
                original = sum(bit << i for i, bit in enumerate(values))
                extended = reduction.lift_witness(original)
                self.assertEqual(reduction.project_witness(extended), original)

    def test_size_bounds_padding_and_fresh_names(self):
        variables = ("__pnp_clause_0_helper_0", "b", "c")
        reduction = three_cnf_to_two_cnf_xor(variables, ((1,), (-1, 2), (1, -2, 3)))
        self.assertEqual(len(reduction.affine.variables), 12)
        self.assertEqual(len(set(reduction.affine.variables)), 12)
        self.assertEqual(len(reduction.cnf), 9)
        self.assertTrue(all(len(c) == 2 for c in reduction.cnf))
        self.assertEqual(len(reduction.affine.equations), 3)
        self.assertTrue(all(mask.bit_count() == 3 and rhs == 0 for mask, rhs in reduction.affine.equations))
        for mask in range(8):
            values = tuple((mask >> i) & 1 for i in range(3))
            if raw_cnf(reduction.original_cnf, values):
                self.assertEqual(reduction.project_witness(reduction.lift_witness(mask)), mask)
            else:
                with self.assertRaises(ValueError):
                    reduction.lift_witness(mask)

    def test_empty_and_invalid_inputs(self):
        self.assertEqual(three_cnf_to_two_cnf_xor((), ()).lift_witness(0), 0)
        empty = three_cnf_to_two_cnf_xor((), ((),))
        self.assertEqual(empty.cnf, ((),))
        with self.assertRaises(ValueError):
            empty.lift_witness(0)
        for bad in (((0,),), ((2,),), ((True,),), ((1, 1, 1, 1),)):
            with self.assertRaises(ValueError):
                three_cnf_to_two_cnf_xor(("a",), bad)


if __name__ == "__main__":
    unittest.main()
