"""Use raw Cartesian products as a reference for the support decider."""

from functools import reduce
from itertools import product
from operator import xor
import random
import unittest

from pnp_lab.frontier import decide_signature_supports


def sums(groups):
    return {reduce(xor, chosen, 0) for chosen in product(*groups)}


class FrontierDecisionTests(unittest.TestCase):
    def check(self, groups, rhs, expected, **kwargs):
        r = decide_signature_supports(groups, rhs, **kwargs)
        self.assertEqual(r["status"], expected)
        if expected == "SAT":
            self.assertEqual(len(r["witness"]), len(groups))
            self.assertTrue(all(x in g for x, g in zip(r["witness"], groups)))
            self.assertEqual(reduce(xor, r["witness"], 0), rhs)
        else:
            self.assertIsNone(r["witness"])
        for width, dim in zip(r["state_counts"], r["cut_ranks"]):
            self.assertLessEqual(width, 1 << dim)
        return r

    def test_all_two_group_supports_in_two_bits(self):
        choices = [tuple(i for i in range(4) if subset >> i & 1) for subset in range(16)]
        for g, h in product(choices, repeat=2):
            feasible = sums((g, h))
            for rhs in range(4):
                with self.subTest(g=g, h=h, rhs=rhs):
                    self.check((g, h), rhs, "SAT" if rhs in feasible else "UNSAT")

    def test_mixed_groups_against_independent_cartesian_oracle(self):
        rng = random.Random(350771)
        for trial in range(180):
            groups = [tuple(rng.randrange(32) for _ in range(rng.randint(1, 5)))
                      for _ in range(rng.randint(0, 5))]
            feasible = sums(groups)
            rhs = rng.choice(sorted(feasible)) if trial % 3 == 0 else rng.randrange(32)
            with self.subTest(trial=trial):
                self.check(groups, rhs, "SAT" if rhs in feasible else "UNSAT")
                budget = rng.randrange(12)
                r = decide_signature_supports(groups, rhs, max_transitions=budget)
                self.assertLessEqual(r["transitions"], budget)
                if r["status"] != "UNKNOWN":
                    self.assertEqual(r["status"], "SAT" if rhs in feasible else "UNSAT")
                else:
                    self.assertIsNone(r["witness"])

    def test_affine_absorption_cascade_with_original_witnesses(self):
        # Exactly one group becomes affine in each pass. Several options
        # collide after projection, so simply returning quotient masks fails.
        base = [(0, 4, 8), (0, 2, 4), (0, 1, 2), (0, 1)]
        shifts = [260, 1, 11, 514]
        groups = [tuple(x ^ s for x in g) for g, s in zip(base, shifts)]
        feasible = sums(groups)
        self.assertEqual(len(feasible), 16)
        for rhs in feasible:
            r = self.check(groups, rhs, "SAT", max_transitions=0)
            self.assertEqual(r["affine_groups_by_round"], [1, 1, 1, 1])
            self.assertEqual(r["affine_rank"], 4)
            self.assertEqual(r["residual_groups"], 0)
            self.assertEqual(r["transitions"], 0)
        self.check(groups, min(feasible) ^ (1 << 200), "UNSAT", max_transitions=0)

    def test_power_of_two_size_is_not_sufficient_for_affinity(self):
        # These four vectors have a 3-dimensional affine hull (8 elements).
        g = [(0, 1, 2, 4)]
        r = self.check(g, 3, "UNSAT")
        self.assertEqual(r["affine_groups"], 0)
        self.assertEqual(r["reason"], "empty_frontier")
        self.assertEqual(r["transitions"], 4)

    def test_suffix_hull_prunes_noncoordinate_inconsistency(self):
        # Every coordinate of the second group varies, but contributions
        # always have equal low bits. A retired-coordinate-only test misses it.
        r = self.check([(0, 1, 2), (0, 3, 12)], 1, "SAT")
        self.assertEqual(r["state_counts"], [1, 2, 1])
        self.assertEqual(r["cut_ranks"], [0, 1, 0])
        self.assertGreaterEqual(r["suffix_pruned"], 1)

    def test_residual_decision_and_reverse_lift_coexist(self):
        # Two affine groups have overlapping, noncoordinate directions;
        # nonlinear groups survive. Witnesses must use original translated masks.
        groups = [(0, 24, 96, 120), (6, 30), (129, 130, 132), (3, 5, 7)]
        feasible = sums(groups)
        for rhs in range(256):
            r = self.check(groups, rhs, "SAT" if rhs in feasible else "UNSAT")
            self.assertEqual(r["affine_groups"], 2)
            self.assertEqual(r["residual_indices"], [2, 3])

    def test_budget_boundaries_and_shortcuts(self):
        g = [(0, 1, 2)]
        partial = self.check(g, 3, "UNKNOWN", max_transitions=2)
        self.assertEqual(partial["transitions"], 2)
        self.check(g, 3, "UNSAT", max_transitions=3)
        self.check(g, 4, "UNSAT", max_transitions=0)  # outside the affine hull
        self.check(g, 0, "SAT", max_transitions=1)  # first actual terminal witness
        self.check(g, 0, "UNKNOWN", max_transitions=0)
        incomplete = self.check([(0, 1, 2), (0, 3, 12)], 1, "UNKNOWN", max_transitions=2)
        self.assertEqual(incomplete["partial_states"], 1)
        self.assertEqual(incomplete["state_counts"], [1])

    def test_explicit_frontier_can_remain_exponential(self):
        # Each independent two-bit block has three possibilities. At the
        # middle cut its matching group is still in the suffix. All 3^m
        # distinct prefix sums survive, though reordering this family is easy.
        for m in range(1, 6):
            left = [(0, 1 << (2*i), 2 << (2*i)) for i in range(m)]
            r = self.check(left + left, 0, "SAT")
            self.assertEqual(r["affine_groups"], 0)
            self.assertEqual(r["state_counts"][m], 3 ** m)
            self.assertEqual(r["peak_states"], 3 ** m)
            self.assertEqual(r["peak_cut_rank"], 2*m)

    def test_duplicate_masks_empty_inputs_and_high_coordinates(self):
        self.check([], 0, "SAT", max_transitions=0)
        self.check([], 1, "UNSAT", max_transitions=0)
        self.check([[1], []], 1, "UNSAT", max_transitions=0)
        b = 1 << 401
        masks = [(b ^ 9, b ^ 9, 1), (b, 8, b)]
        for rhs in sums(masks):
            self.check(masks, rhs, "SAT", max_transitions=0)
        self.assertEqual(decide_signature_supports((iter(g) for g in masks), 9)["status"], "SAT")

    def test_validate_entire_input_before_early_answers(self):
        for value in (-1, True, 1.5, "7", None):
            with self.assertRaises(ValueError):
                decide_signature_supports([[], (value,)], 0)
            with self.assertRaises(ValueError):
                decide_signature_supports([], value)
        for value in (-1, True, "1", 1.0):
            with self.assertRaises(ValueError):
                decide_signature_supports([[]], 0, max_transitions=value)
        for groups in ("", [""], [b""], [None], 1):
            with self.assertRaises(ValueError):
                decide_signature_supports(groups, 0)
