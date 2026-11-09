import copy
from itertools import product
import math
import random
import unittest

from pnp_lab.sat_scaling import (brute_force, check_refutation, check_row_contradiction,
                                dpll, fit_growth, gaussian, graph_xor_cnf,
                                random_three_cnf, recognize_xor, satisfies,
                                xor_clauses)


class ScalingTests(unittest.TestCase):
    def assert_answer(self, n, clauses, answer):
        expected = brute_force(n, clauses)
        self.assertEqual(answer["status"], "SAT" if expected is not None else "UNSAT")
        if expected is not None:
            self.assertTrue(satisfies(clauses, answer["witness"]))
        else:
            self.assertTrue(check_refutation(n, clauses, answer["proof"]))

    def test_all_subsets_of_three_literal_clauses_against_truth_tables(self):
        universe = list(product((1, -1), (2, -2), (3, -3)))
        for mask in range(256):
            clauses = [c for i, c in enumerate(universe) if mask & (1 << i)]
            for heuristic in ("first", "shortest"):
                self.assert_answer(3, clauses, dpll(3, clauses, heuristic, None))

    def test_mixed_width_random_cnf_and_constants(self):
        rng = random.Random(8831)
        for n in range(7):
            for _ in range(20):
                clauses = []
                for _ in range(rng.randrange(15)):
                    scope = rng.sample(range(1, n + 1), rng.randrange(min(n, 4) + 1))
                    clauses.append(tuple(v if rng.getrandbits(1) else -v for v in scope))
                for heuristic in ("first", "shortest"):
                    self.assert_answer(n, clauses, dpll(n, clauses, heuristic, None))

    def test_refutation_checker_rejects_corruption(self):
        clauses = list(product((1, -1), (2, -2), (3, -3)))
        result = dpll(3, clauses, budget=None)
        self.assertTrue(check_refutation(3, clauses, result["proof"]))
        proof = copy.deepcopy(result["proof"])
        del proof["children"]["1"]
        self.assertFalse(check_refutation(3, clauses, proof))
        proof = copy.deepcopy(result["proof"])
        proof["variable"] = 0
        self.assertFalse(check_refutation(3, clauses, proof))
        proof = dpll(1, [(1,), (-1,)], budget=None)["proof"]
        proof["units"][0] = (1, 1)
        self.assertFalse(check_refutation(1, [(1,), (-1,)], proof))
        self.assertFalse(check_refutation(1, [(1,)], {"units": [], "conflict": 0}))

    def test_work_limit_is_unknown_and_invalid_input_is_rejected(self):
        for clauses in ([(1,)], [(1,), (-1,)]):
            result = dpll(1, clauses, budget=0)
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertIsNone(result["witness"])
            self.assertIsNone(result["proof"])
        for clauses in ([(0,)], [(2,)], [(1, -1)]):
            with self.assertRaises(ValueError):
                dpll(1, clauses)
        with self.assertRaises(ValueError):
            dpll(1, [(1,)], budget=-1)

    def test_gaussian_answers_and_recovered_cnf_against_enumeration(self):
        rng = random.Random(712)
        for n in range(3, 8):
            for _ in range(16):
                scopes = list(__import__("itertools").combinations(range(1, n + 1), 3))
                rng.shuffle(scopes)
                clauses = []
                for scope in scopes[:min(len(scopes), 10)]:
                    clauses.extend(xor_clauses(scope, rng.getrandbits(1)))
                equations = recognize_xor(n, clauses)
                self.assertIsNotNone(equations)
                for word in range(1 << n):
                    self.assertEqual(satisfies(clauses, word),
                                     all((mask & word).bit_count() % 2 == rhs for mask, rhs in equations))
                answer = gaussian(n, equations)
                expected = brute_force(n, clauses)
                self.assertEqual(answer["status"], "SAT" if expected is not None else "UNSAT")
                if expected is None:
                    self.assertTrue(check_row_contradiction(equations, answer["contradiction"]))
                else:
                    self.assertTrue(satisfies(clauses, answer["witness"]))
        self.assertFalse(check_row_contradiction([(1, 0), (1, 1)], 1))
        self.assertTrue(check_row_contradiction([(1, 0), (1, 1)], 3))

    def test_parity_recognizer_rejects_incomplete_or_mixed_blocks(self):
        clauses = xor_clauses((1, 2, 3), 1)
        self.assertIsNone(recognize_xor(3, clauses[:-1]))
        self.assertIsNone(recognize_xor(3, clauses + [(1,)]))
        self.assertIsNone(recognize_xor(3, clauses + xor_clauses((1, 2, 3), 0)))

    def test_graph_controls_use_original_cnf_and_both_answers(self):
        for n in (12, 15, 18):
            for odd in (False, True):
                clauses = graph_xor_cnf(n, odd, 91)
                self.assertEqual(len(clauses), 8 * n // 3)
                equations = recognize_xor(n, clauses)
                answer = gaussian(n, equations)
                self.assertEqual(answer["status"], "UNSAT" if odd else "SAT")
                if odd:
                    self.assertTrue(check_row_contradiction(equations, answer["contradiction"]))
                else:
                    self.assertTrue(satisfies(clauses, answer["witness"]))
                if n == 12:
                    self.assert_answer(n, clauses, dpll(n, clauses, budget=None))
        self.assertEqual(random_three_cnf(12, 17, 4, 19), random_three_cnf(12, 17, 4, 19))

    def test_growth_models_on_known_synthetic_data(self):
        sizes = [12, 18, 24, 30, 36, 42, 48, 54, 60]
        features = {"polynomial": math.log2, "exponential": float, "sqrt_exponential": math.sqrt}
        for name, feature in features.items():
            costs = [2 ** (2 + .3 * feature(n)) - 1 for n in sizes]
            fits = fit_growth(sizes, costs, 6)
            self.assertEqual(fits[name]["held_out_log2_rmse"], 0)
            self.assertEqual(min(fits, key=lambda k: fits[k]["held_out_log2_rmse"]), name)

    def test_censored_upper_median_is_not_solved_only_median(self):
        # Capped observations belong in the denominator; censoring six of
        # sixteen still permits the ninth order statistic, censoring eight does not.
        import importlib.util
        from pathlib import Path
        path = Path(__file__).resolve().parents[1] / "experiments/sat_scaling.py"
        spec = importlib.util.spec_from_file_location("scaling_experiment", path)
        experiment = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(experiment)
        for completed, exact in ((10, True), (8, False)):
            records = [{"status": "SAT", "literal_inspections": i} for i in range(completed)]
            records.extend({"status": "UNKNOWN", "literal_inspections": 100} for _ in range(16 - completed))
            median = experiment.quantile_bound(records, 9, 16)
            self.assertEqual(median["exact"], exact)
            self.assertEqual(median["lower_bound"], 8 if exact else 100)


if __name__ == "__main__":
    unittest.main()
