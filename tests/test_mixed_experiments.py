"""Independent semantics and structural controls for the mixed experiments."""

import importlib.util
import itertools
import json
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "mixed_constraints_under_test",
    Path(__file__).resolve().parents[1] / "experiments" / "mixed_constraints.py",
)
assert SPEC is not None and SPEC.loader is not None
mixed = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mixed)


class MixedExperimentTests(unittest.TestCase):
    def test_exactly_one_family_and_constraint_removal_controls(self):
        for k in (3, 4, 5, 6):
            rows, cnf = mixed.exactly_one_even_input(k)
            self.assertEqual(len(cnf), 1 + k * (k - 1) // 2)
            self.assertEqual(sum(map(len, cnf)), k * k)
            self.assertTrue(all(len(clause) >= 2 for clause in cnf))
            for values in itertools.product((0, 1), repeat=k):
                self.assertEqual(mixed.raw_holds((), cnf, values), sum(values) == 1)
            self.assertEqual(mixed.brute_force(k, rows, cnf)["model_count"], 0)
            # Each part of the contradiction matters: these variants have
            # known models, verified on the original formulas without the solver.
            self.assertEqual(mixed.brute_force(k, (), cnf)["model_count"], k)
            self.assertEqual(mixed.brute_force(k, (((1 << k) - 1, 1),), cnf)["model_count"], k)
            self.assertEqual(mixed.brute_force(k, rows, cnf[1:])["model_count"], 1)
            self.assertEqual(mixed.brute_force(k, rows, cnf[:1] + cnf[2:])["model_count"], 1)

    def test_structural_enumeration_count_and_small_certificates(self):
        for k in (3, 6, 9):
            case = mixed.verify_enumeration_barrier(k)
            self.assertEqual(case["solver"]["checked_cells"], 1 << (k - 1))
            self.assertEqual(case["solver"]["effective_rank"], k - 1)
            self.assertFalse(case["exhaustive_requested"])
            if k <= 6:
                self.assertTrue(case["full_certificate_checked"])

    def test_large_free_dimension_does_not_force_large_observed_rank(self):
        for n in (6, 9, 64, 256):
            case = mixed.verify_low_rank(n)
            dimension = n - 3 * (n // 6)
            self.assertEqual(case["solver"]["affine_dimension"], dimension)
            self.assertEqual(case["solver"]["checked_cells"], 8)
            self.assertEqual(case["solver"]["model_count"], 3 * (1 << (dimension - 3)))
            if n <= 10:
                self.assertEqual(case["independent_oracle"]["model_count"], case["predicted_model_count"])
            else:
                self.assertIsNone(case["independent_oracle"])

    def test_fixed_seed_cases_against_raw_full_enumeration(self):
        report = mixed.verify_random_oracle(random_cases=96)
        self.assertEqual(report["random_cases"], 96)
        self.assertEqual(len(report["cases"]), 96 + report["curated_cases"])
        self.assertLessEqual(report["max_variables"], 7)
        self.assertGreater(report["sat_cases"], 0)
        self.assertGreater(report["unsat_cases"], 0)
        self.assertGreaterEqual(report["random_planted_consistent_xor_cases"], 48)
        self.assertGreaterEqual(report["random_coverage"]["affine_consistent"], 48)
        self.assertGreater(report["random_coverage"]["consistent_xor_but_mixed_unsat"], 0)
        self.assertGreater(report["random_coverage"]["rank_less_than_dimension"], 0)
        self.assertGreater(report["random_coverage"]["rank_equal_dimension"], 0)
        self.assertGreater(report["random_coverage"]["positive_rank_less_than_dimension"], 0)
        self.assertGreater(report["random_coverage"]["positive_rank_equal_dimension"], 0)
        self.assertTrue(all(case["checks_passed"] for case in report["cases"]))

    def test_incomplete_coverage_remains_unknown(self):
        case = mixed.verify_budget_control()
        self.assertEqual(case["solver"]["status"], "UNKNOWN")
        self.assertIsNone(case["solver"]["model_count"])
        self.assertEqual(case["solver"]["checked_cells"], 3)

    def test_report_is_deterministic_and_does_not_embed_full_certificates(self):
        first = mixed.run_experiment([9, 6], [4, 3], random_cases=12)
        second = mixed.run_experiment([6, 9, 6], [3, 4], random_cases=12)
        self.assertEqual(json.dumps(first, sort_keys=True), json.dumps(second, sort_keys=True))
        self.assertTrue(first["all_checks_passed"])
        for case in first["low_rank_cases"] + first["enumeration_barrier_cases"]:
            self.assertNotIn("trace", case["solver"])
            self.assertNotIn("certificate", case["solver"])


if __name__ == "__main__":
    unittest.main()
