"""Independent resolution checker and finite raw-CNF controls for Phase 28."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
import unittest

from experiments.tseitin_resolution_miter import (
    certificate, check_certificate, finite_semantic_control, miter, report, verify)


def independent_replay(proof):
    """Replay from signed-literal sets without using the generator or its checker."""
    n = proof["variables"]
    lines = []
    for c in proof["axioms"]:
        values = set(c)
        assert values and all(0 < abs(v) <= n for v in values)
        assert all(-v not in values for v in values)
        lines.append(values)
    for s in proof["steps"]:
        assert 0 <= s["left"] < len(lines)
        assert 0 <= s["right"] < len(lines)
        lhs, rhs, pivot = lines[s["left"]], lines[s["right"]], s["pivot"]
        assert pivot in lhs and -pivot in rhs
        result = (lhs - {pivot}) | (rhs - {-pivot})
        assert all(-v not in result for v in result)
        assert result == set(s["clause"])
        assert len(result) <= 3
        lines.append(result)
    assert not lines[-1]
    return len(lines)


def raw_truth(clause, bits):
    """Independent literal interpreter, no call to eval_clause."""
    for lit in clause:
        b = (bits >> (abs(lit)-1)) % 2
        if (lit > 0 and b == 1) or (lit < 0 and b == 0):
            return True
    return False


class TseitinResolutionMiterTests(unittest.TestCase):
    def test_unbounded_template_bounded_checkpoints(self):
        for m in (1,2,3,7,16):
            proof = certificate(m)
            self.assertEqual(independent_replay(proof), 32*m-18)
            self.assertEqual(check_certificate(proof)["derived"], 18*m-12)
            self.assertEqual(check_certificate(proof)["max_width"], 3)
            self.assertEqual(len(proof["axioms"]), 14*m-6)
            self.assertEqual(len(proof["steps"]), 18*m-12)
        self.assertGreater((1<<16)-1, 32*16-18)

    def test_miter_semantics_exhaustive_only_m1_m2(self):
        for m in (1,2):
            n, cnf = miter(m)
            self.assertEqual(n,6*m-2)
            self.assertEqual(sum(all(raw_truth(c,z) for c in cnf)
                                 for z in range(1<<n)), 0)
            equal_outputs = cnf[:-1] + ((-cnf[-1][0],),)
            self.assertEqual(sum(all(raw_truth(c,z) for c in equal_outputs)
                                 for z in range(1<<n)),
                             (2**m-1)*2**(m-1))
            self.assertEqual(finite_semantic_control(m)["miter_models"], 0)

    def test_satisfiable_sibling_explicit_large_witness(self):
        for m in (1,2,3,7,16):
            n, cnf = miter(m)
            # Choose x0=y0=1; all other original inputs zero.
            # Every p0 and every subsequent prefix XOR is 1, in both copies.
            selected = [1,m+1,2*m+1,4*m]
            selected += [3*m+i for i in range(1,m)]
            selected += [5*m-1+i for i in range(1,m)]
            z = sum(1<<(v-1) for v in selected)
            self.assertLess(z, 1<<n)
            sibling = cnf[:-1] + ((-cnf[-1][0],),)
            self.assertTrue(all(raw_truth(c,z) for c in sibling))
            self.assertFalse(all(raw_truth(c,z) for c in cnf))

    def test_corrupted_resolution_steps_rejected(self):
        original = certificate(2)
        altered = deepcopy(original)
        altered["steps"][0]["pivot"] *= -1
        with self.assertRaises(ValueError):
            check_certificate(altered)
        altered = deepcopy(original)
        altered["steps"][-1]["clause"] = [1]
        with self.assertRaises(ValueError):
            check_certificate(altered)
        altered = deepcopy(original)
        altered["steps"][0]["left"] = len(original["axioms"])+len(original["steps"])
        with self.assertRaises(ValueError):
            check_certificate(altered)
        altered = deepcopy(original)
        altered["axioms"][0] = [9999]
        with self.assertRaises(ValueError):
            check_certificate(altered)

    def test_exact_deterministic_snapshot(self):
        path = Path(__file__).resolve().parents[1] / "results" / "tseitin_resolution_miter.json"
        saved = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(saved, report())
        self.assertEqual(saved["cases"], [verify(m) for m in (1,2,3,7,16)])

    def test_registered_resource_cutoff(self):
        with self.assertRaises(ValueError):
            miter(0)
        with self.assertRaises(ValueError):
            finite_semantic_control(3)
        self.assertTrue(report()["new_lean_theorems"] == 0)


if __name__ == "__main__":
    unittest.main()
