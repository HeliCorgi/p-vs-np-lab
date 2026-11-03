"""End-to-end checks of the published solver entry point and budget semantics."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class MixedCliTests(unittest.TestCase):
    def run_cli(self, *args):
        return subprocess.run([sys.executable, str(ROOT / "scripts/solve_mixed.py"), *map(str, args)],
                              cwd=ROOT, capture_output=True, text=True)

    def test_sat_count_and_original_witness(self):
        process = self.run_cli(ROOT / "examples/mixed_sat.json", "--count-models")
        self.assertEqual(process.returncode, 0, process.stderr)
        result = json.loads(process.stdout)
        self.assertEqual(result["status"], "SAT")
        self.assertEqual(result["model_count"], 4)
        self.assertEqual(result["effective_rank"], 2)
        witness = result["witness_mask"]
        a, b, c, d = ((witness >> i) & 1 for i in range(4))
        self.assertTrue(a == b and c == d and (a or c) and (not b or not d))

    def test_unsat_certificate_can_be_verified(self):
        process = self.run_cli(ROOT / "examples/mixed_unsat.json", "--verify-certificate")
        self.assertEqual(process.returncode, 0, process.stderr)
        result = json.loads(process.stdout)
        self.assertEqual(result["status"], "UNSAT")
        self.assertEqual(result["checked_cells"], 8)
        self.assertIsNotNone(result["certificate"])

    def test_budget_exhaustion_is_not_unsat(self):
        process = self.run_cli(ROOT / "examples/mixed_unsat.json", "--max-cells", 2)
        self.assertEqual(process.returncode, 2, process.stderr)
        result = json.loads(process.stdout)
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertIsNone(result["model_count"])
        self.assertIsNone(result["certificate"])

    def test_invalid_literal_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "invalid.json"
            source.write_text('{"variables":["x"],"cnf":[[0]]}', encoding="utf-8")
            process = self.run_cli(source)
        self.assertEqual(process.returncode, 1)
        self.assertEqual(json.loads(process.stderr)["status"], "ERROR")

    def test_usage_error_is_distinct_from_unknown(self):
        process = self.run_cli(ROOT / "examples/mixed_sat.json", "--max-cells", "not-an-integer")
        self.assertEqual(process.returncode, 1)
        self.assertEqual(json.loads(process.stderr)["status"], "ERROR")


if __name__ == "__main__":
    unittest.main()
