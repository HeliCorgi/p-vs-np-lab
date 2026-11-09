import json
from pathlib import Path
import tempfile
import unittest

from pnp_lab.cdcl_audit import (checked_model, dimacs, formula_hash,
                                order_statistic_bounds, regenerate, summarize,
                                verified_output, verify_checker_source)

ROOT = Path(__file__).resolve().parents[1]


class CDCLAuditTests(unittest.TestCase):
    def test_original_cnf_models_reject_false_or_inconsistent_answers(self):
        self.assertEqual(checked_model(3, [(1, -2), (3,)], [1, -2, 3]), 5)
        for model in (None, [-1, 2, -3], [1, -1, 3], [0, 3], [4]):
            with self.assertRaises(ValueError):
                checked_model(3, [(1, -2), (3,)], model)
        self.assertEqual(checked_model(3, [], []), 0)

    def test_checker_requires_exact_success_line_and_success_exit(self):
        self.assertTrue(verified_output(0, "c checking\r\ns VERIFIED\n"))
        self.assertFalse(verified_output(1, "s VERIFIED\n"))
        self.assertFalse(verified_output(0, "s NOT VERIFIED\n"))
        self.assertFalse(verified_output(0, "c s VERIFIED was not reported\n"))
        self.assertFalse(verified_output(0, ""))

    def test_variable_censor_thresholds_need_bounds_on_both_sides(self):
        rows = [{"status": "SAT", "conflicts": x} for x in (2, 4, 100)]
        rows.append({"status": "UNKNOWN", "conflicts": 3})
        self.assertEqual(order_statistic_bounds(rows, 2), dict(lower=3, upper=4, exact=False))
        rows[-1]["conflicts"] = 200
        self.assertEqual(order_statistic_bounds(rows, 2), dict(lower=4, upper=4, exact=True))
        self.assertEqual(order_statistic_bounds(rows, 4), dict(lower=200, upper=None, exact=False))

    def test_order_bounds_do_not_drop_unknown_cases(self):
        rows = [{"status": "UNSAT", "conflicts": i} for i in range(8)]
        rows.extend({"status": "UNKNOWN", "conflicts": 100 + i} for i in range(8))
        self.assertEqual(order_statistic_bounds(rows, 9), dict(lower=100, upper=None, exact=False))
        with self.assertRaises(ValueError):
            order_statistic_bounds(rows, 17)

    def test_no_growth_fit_when_one_median_is_censored(self):
        rows = []
        for n in (96, 144, 192, 240, 288, 336):
            for i in range(16):
                rows.append(dict(panel="extended", family="random_3sat_4.25", solver="example",
                                 n=n, conflicts=n * n + i, propagations=3 * n,
                                 status="UNKNOWN" if n == 336 and i >= 7 else "UNSAT"))
        result = summarize(rows)[0]
        self.assertIsNone(result["fits"])
        self.assertIsNone(result["best_held_out_model"])
        self.assertEqual(result["by_size"][-1]["counts"]["UNKNOWN"], 9)

    def test_paired_formula_hashes_match_all_original_inputs(self):
        report = json.loads((ROOT / "results/sat_scaling.json").read_text())
        for record in report["records"]:
            if record["heuristic"] == "first":
                clauses = regenerate(record["family"], record["n"], record["seed"])
                self.assertEqual(formula_hash(clauses), record["formula_sha256"])
        self.assertEqual(dimacs(2, [(1, -2), ()]), "p cnf 2 2\n1 -2 0\n 0\n")

    def test_checker_snapshot_and_source_tampering(self):
        verify_checker_source(ROOT)
        with tempfile.TemporaryDirectory() as temp:
            target = Path(temp) / "third_party/drat_trim"
            target.mkdir(parents=True)
            for name in ("manifest.json", "LICENSE", "drat-trim.c"):
                (target / name).write_bytes((ROOT / "third_party/drat_trim" / name).read_bytes())
            (target / "drat-trim.c").write_text("changed")
            with self.assertRaises(ValueError):
                verify_checker_source(temp)


if __name__ == "__main__":
    unittest.main()
