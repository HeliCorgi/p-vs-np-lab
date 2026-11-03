"""Parity-cut soundness, model preservation, certificates, and limitations."""

from copy import deepcopy
from itertools import combinations, product
import json
import random
import unittest
from unittest.mock import patch

from pnp_lab.affine import AffineRelation
from pnp_lab.mixed import solve_mixed
from pnp_lab.parity_cuts import (
    check_parity_cut_certificate,
    check_parity_cut_unsat_certificate,
    derive_parity_cuts,
    solve_with_parity_cuts,
)


def original_models(n, raw_rows, raw_cnf):
    """Exhaust original bits directly, without either solver's normalization."""
    models = set()
    for bits in product((0, 1), repeat=n):
        if any(sum(bits[i] for i in range(n) if (mask >> i) & 1) % 2 != rhs
               for mask, rhs in raw_rows):
            continue
        if all(any(bits[abs(literal) - 1] == (literal > 0) for literal in clause)
               for clause in raw_cnf):
            models.add(sum(bit << i for i, bit in enumerate(bits)))
    return models


def exactly_one(literals):
    literals = tuple(literals)
    return (literals,) + tuple((-left, -right) for left, right in combinations(literals, 2))


def exactly_two(k):
    return (tuple(tuple(j for j in range(1, k + 1) if j != i) for i in range(1, k + 1))
            + tuple(tuple(-j for j in triple) for triple in combinations(range(1, k + 1), 3)))


class ParityCutTests(unittest.TestCase):
    def test_all_signed_exactly_one_blocks_preserve_models(self):
        for width in range(1, 6):
            for signs in product((-1, 1), repeat=width):
                literals = tuple((i + 1) * sign for i, sign in enumerate(signs))
                cnf = exactly_one(literals)
                # Include two genuinely unconstrained original variables.
                n = width + 2
                affine = AffineRelation.truth(tuple(f"x{i}" for i in range(n)))
                result = solve_with_parity_cuts(affine, cnf, include_trace=False)
                expected = original_models(n, (), cnf)
                self.assertEqual(result["status"], "SAT")
                self.assertEqual(result["model_count"], width * 4)
                self.assertEqual(result["model_count"], len(expected))
                self.assertIn(result["witness_mask"], expected)
                proof = result["preprocessing"]["derivation"]
                self.assertTrue(check_parity_cut_certificate(affine, cnf, proof))
                expected_row = [(1 << width) - 1, 1 ^ (signs.count(-1) & 1)]
                self.assertTrue(all(cut["equation"] == expected_row for cut in proof["cuts"]))
                rows = tuple(tuple(cut["equation"]) for cut in proof["cuts"])
                self.assertEqual(original_models(n, rows, cnf), expected)
                self.assertEqual(result["preprocessing"]["strengthened_affine_rank"], 1)
                self.assertEqual(result["effective_rank"], width - 1)
                self.assertEqual(result["omitted_affine_directions"], 2)

    def test_fixed_seed_formulas_against_original_raw_semantics(self):
        rng = random.Random(3141104)
        sat = unsat = cut_cases = 0
        for trial in range(180):
            n = rng.randrange(8)
            names = tuple(f"v{i}" for i in range(n))
            planted = rng.randrange(1 << n)
            raw_rows = tuple((mask, ((mask & planted).bit_count() & 1)
                              if trial % 4 else rng.randrange(2))
                             for mask in (rng.randrange(1 << n) for _ in range(rng.randrange(n + 2))))
            clauses = []
            if n:
                for _ in range(rng.randrange(6)):
                    clauses.append(tuple(rng.choice((-1, 1)) * rng.randrange(1, n + 1)
                                         for _ in range(rng.randrange(1, 5))))
                if trial % 3 == 0:
                    variables = rng.sample(range(1, n + 1), rng.randrange(1, min(n, 5) + 1))
                    clauses.extend(exactly_one(rng.choice((-1, 1)) * i for i in variables))
            if trial % 17 == 0:
                clauses.append(())
            raw_cnf = tuple(clauses)
            affine = AffineRelation(names, raw_rows)
            expected = original_models(n, raw_rows, raw_cnf)
            result = solve_with_parity_cuts(affine, (iter(clause) for clause in raw_cnf),
                                            include_certificate=True, include_trace=False)
            self.assertEqual(result["status"], "SAT" if expected else "UNSAT", (trial, raw_rows, raw_cnf))
            self.assertEqual(result["model_count"], len(expected), (trial, raw_rows, raw_cnf))
            self.assertTrue(result["exhaustive"])
            self.assertEqual(result["trace"], [])
            metadata = result["preprocessing"]
            proof = metadata["derivation"]
            self.assertTrue(metadata["certificate_checked"])
            self.assertTrue(check_parity_cut_certificate(affine, raw_cnf, proof))
            if proof["cuts"]:
                cut_cases += 1
            cut_rows = tuple(tuple(cut["equation"]) for cut in proof["cuts"])
            # Check the stronger property: cuts follow from CNF alone, even
            # for assignments outside the original affine solution set.
            self.assertEqual(original_models(n, (), raw_cnf), original_models(n, cut_rows, raw_cnf))
            self.assertEqual(expected, original_models(n, raw_rows + cut_rows, raw_cnf))
            if expected:
                sat += 1
                self.assertIn(result["witness_mask"], expected)
                self.assertIsNone(result["certificate"])
            else:
                unsat += 1
                certificate = json.loads(json.dumps(result["certificate"]))
                self.assertTrue(check_parity_cut_unsat_certificate(affine, raw_cnf, certificate))
            if metadata["strengthened_affine_rank"] is not None:
                old = solve_mixed(affine, raw_cnf, max_cells=0, include_trace=False)
                self.assertEqual(old["affine_dimension"] - old["effective_rank"],
                                 result["affine_dimension"] - result["effective_rank"])
                self.assertLessEqual(result["effective_rank"], old["effective_rank"])
        self.assertGreater(sat, 20)
        self.assertGreater(unsat, 20)
        self.assertGreater(cut_cases, 40)

    def test_previous_exactly_one_barrier_has_a_zero_cell_refutation(self):
        for k in (3, 8, 16, 32):
            affine = AffineRelation(tuple(f"x{i}" for i in range(k)), (((1 << k) - 1, 0),))
            cnf = exactly_one(range(1, k + 1))
            result = solve_with_parity_cuts(affine, cnf, exhaustive=False,
                                            max_cells=0, include_certificate=True, include_trace=False)
            self.assertEqual(result["status"], "UNSAT")
            self.assertEqual(result["reason"], "certified_linear_contradiction")
            self.assertEqual(result["checked_cells"], 0)
            self.assertEqual(result["model_count"], 0)
            self.assertTrue(result["exhaustive"])
            self.assertFalse(result["preprocessing"]["fallback_used"])
            self.assertEqual(result["preprocessing"]["derived_cut_count"], 1)
            self.assertEqual(result["preprocessing"]["original_free_dimension"], k - 1)
            self.assertIsNone(result["preprocessing"]["strengthened_free_dimension"])
            self.assertEqual(result["certificate"]["derivation"]["contradiction"]["combination"], [0, 1])
            self.assertTrue(check_parity_cut_unsat_certificate(affine, cnf, result["certificate"]))

    def test_overlapping_cuts_refute_an_odd_cycle_globally(self):
        for k in (3, 5, 7, 21):
            affine = AffineRelation.truth(tuple(f"x{i}" for i in range(k)))
            cnf = tuple(clause for i in range(1, k + 1)
                        for clause in ((i, i % k + 1), (-i, -(i % k + 1))))
            result = solve_with_parity_cuts(affine, cnf, max_cells=0, include_certificate=True)
            self.assertEqual(result["status"], "UNSAT")
            self.assertEqual(result["checked_cells"], 0)
            self.assertEqual(result["preprocessing"]["derived_cut_count"], 2 * k)
            self.assertEqual(len(result["certificate"]["derivation"]["contradiction"]["combination"]), k)
            self.assertTrue(check_parity_cut_unsat_certificate(affine, cnf, result["certificate"]))

    def test_natural_exactly_two_barrier_requires_fallback(self):
        for k in (4, 5, 7):
            affine = AffineRelation(tuple(f"x{i}" for i in range(k)), (((1 << k) - 1, 1),))
            cnf = exactly_two(k)
            self.assertEqual(len(original_models(k, (), cnf)), k * (k - 1) // 2)
            result = solve_with_parity_cuts(affine, cnf, exhaustive=False,
                                            include_certificate=True, include_trace=False)
            self.assertEqual(result["status"], "UNSAT")
            self.assertEqual(result["preprocessing"]["derived_cut_count"], 0)
            self.assertFalse(result["preprocessing"]["contradiction_found"])
            self.assertTrue(result["preprocessing"]["fallback_used"])
            self.assertEqual(result["effective_rank"], k - 1)
            self.assertEqual(result["checked_cells"], 1 << (k - 1))
            self.assertTrue(check_parity_cut_unsat_certificate(affine, cnf, result["certificate"]))
            limited = solve_with_parity_cuts(affine, cnf, max_cells=3, include_certificate=True)
            self.assertEqual(limited["status"], "UNKNOWN")
            self.assertEqual(limited["checked_cells"], 3)
            self.assertIsNone(limited["model_count"])
            self.assertIsNone(limited["certificate"])

    def test_normalization_trace_and_budget_semantics(self):
        affine = AffineRelation.truth(("a", "b", "free"))
        cnf = ((1, 1, 2), (-1, -2, -2), (2, 1), (1, -1, 3))
        result = solve_with_parity_cuts(affine, cnf)
        self.assertEqual(result["preprocessing"]["derived_cut_count"], 2)
        self.assertEqual(result["normalized_clause_count"], 2)
        self.assertEqual(result["input_clause_count"], 4)
        self.assertEqual(result["model_count"], 4)
        self.assertEqual(result["checked_cells"], 2)
        self.assertEqual([row["satisfied_clause_count"] for row in result["trace"]], [4, 4])
        self.assertIsNone(result["certificate"])
        self.assertTrue(check_parity_cut_certificate(affine, cnf, result["preprocessing"]["derivation"]))
        early = solve_with_parity_cuts(affine, cnf, exhaustive=False, max_cells=1)
        self.assertEqual(early["status"], "SAT")
        self.assertEqual(early["checked_cells"], 1)
        self.assertFalse(early["exhaustive"])
        self.assertIsNone(early["model_count"])
        zero = solve_with_parity_cuts(affine, cnf, max_cells=0)
        self.assertEqual(zero["status"], "UNKNOWN")
        self.assertFalse(zero["exhaustive"])
        self.assertIsNone(zero["model_count"])
        # Merely deriving an implied parity must never drop the original CNF:
        # odd parity allows all three true, but exactly-one does not.
        strict = solve_with_parity_cuts(affine, exactly_one((1, 2, 3)))
        self.assertEqual(strict["model_count"], 3)
        self.assertEqual(strict["rejecting_cells"], 1)

    def test_empty_scope_empty_clause_units_and_inconsistent_input(self):
        empty = AffineRelation.truth()
        self.assertEqual(solve_with_parity_cuts(empty, ())["model_count"], 1)
        self.assertEqual(solve_with_parity_cuts(empty, (), max_cells=0)["status"], "UNKNOWN")
        false_cnf = solve_with_parity_cuts(empty, ((),), max_cells=0, include_certificate=True)
        self.assertEqual(false_cnf["status"], "UNSAT")
        self.assertEqual(false_cnf["checked_cells"], 0)
        self.assertEqual(false_cnf["preprocessing"]["derivation"]["cuts"][0]["equation"], [0, 1])
        self.assertTrue(check_parity_cut_unsat_certificate(empty, ((),), false_cnf["certificate"]))
        false_affine = AffineRelation.false(("a",))
        contradictory = solve_with_parity_cuts(false_affine, (), max_cells=0, include_certificate=True)
        self.assertEqual(contradictory["status"], "UNSAT")
        self.assertEqual(contradictory["preprocessing"]["derived_cut_count"], 0)
        self.assertEqual(contradictory["certificate"]["derivation"]["contradiction"]["combination"], [0])
        self.assertIsNone(contradictory["preprocessing"]["original_affine_rank"])
        self.assertTrue(check_parity_cut_unsat_certificate(false_affine, (), contradictory["certificate"]))
        one = AffineRelation.truth(("a", "spare"))
        for cnf, expected_bit in ((((1, 1),), 1), (((-1,),), 0)):
            result = solve_with_parity_cuts(one, cnf)
            self.assertEqual(result["model_count"], 2)
            self.assertEqual(result["witness_mask"] & 1, expected_bit)
            self.assertEqual(result["effective_rank"], 0)
        opposite_units = ((1,), (-1,))
        impossible = solve_with_parity_cuts(one, opposite_units, include_certificate=True, max_cells=0)
        self.assertTrue(check_parity_cut_unsat_certificate(one, opposite_units, impossible["certificate"]))

    def test_cut_and_linear_certificates_reject_corruption_without_solving(self):
        affine = AffineRelation(tuple("abcd"), ((7, 0),))
        cnf = exactly_one((-1, 2, -3))
        result = solve_with_parity_cuts(affine, cnf, include_certificate=True)
        proof = result["preprocessing"]["derivation"]
        self.assertIsNotNone(proof["contradiction"])
        mutations = []
        for key, value in (("cover_clause", True), ("cover_clause", len(cnf)),
                           ("exclusion_clauses", [1, 1, 3]),
                           ("exclusion_clauses", [1, 2]),
                           ("exclusion_clauses", [2, 1, 3]),
                           ("exclusion_clauses", [True, 2, 3]),
                           ("equation", [7, 0]), ("equation", [15, 1]),
                           ("equation", [7, True])):
            candidate = deepcopy(proof)
            candidate["cuts"][0][key] = value
            mutations.append(candidate)
        candidate = deepcopy(proof)
        candidate["cuts"].append(deepcopy(candidate["cuts"][0]))
        mutations.append(candidate)
        for combination in ([], [0], [1], [0, 0, 1], [True, 1], [1, 0], [0, 2]):
            candidate = deepcopy(proof)
            candidate["contradiction"]["combination"] = combination
            mutations.append(candidate)
        for claimed in ([0, 0], [1, 1], [False, 1]):
            candidate = deepcopy(proof)
            candidate["contradiction"]["equation"] = claimed
            mutations.append(candidate)
        for key in ("n_variables", "input_clause_count", "input_affine_row_count"):
            candidate = deepcopy(proof)
            candidate[key] = True
            mutations.append(candidate)
        for candidate in mutations:
            self.assertFalse(check_parity_cut_certificate(affine, cnf, candidate), candidate)
        changed = (cnf[0], (1, 2), *cnf[2:])
        self.assertFalse(check_parity_cut_certificate(affine, changed, proof))
        self.assertFalse(check_parity_cut_certificate(AffineRelation(tuple("abcd"), ((7, 1),)), cnf, proof))
        # Certificate checking must not silently rerun either generator, the
        # solver, the finder's normalization, or Gaussian elimination.
        with patch("pnp_lab.parity_cuts.derive_parity_cuts", side_effect=AssertionError("finder called")), \
             patch("pnp_lab.parity_cuts._linear_contradiction", side_effect=AssertionError("eliminator called")), \
             patch("pnp_lab.parity_cuts._normalize_cnf", side_effect=AssertionError("normalizer called")), \
             patch("pnp_lab.affine._rref", side_effect=AssertionError("RREF called")), \
             patch("pnp_lab.parity_cuts.solve_mixed", side_effect=AssertionError("solver called")):
            self.assertTrue(check_parity_cut_certificate(affine, cnf, proof))
            self.assertTrue(check_parity_cut_unsat_certificate(affine, cnf, result["certificate"]))

    def test_derivations_are_not_automatically_unsat_proofs(self):
        affine = AffineRelation.truth(("a", "b", "c", "d"))
        cnf = exactly_one((1, 2, 3))
        derivation = derive_parity_cuts(affine, cnf)
        self.assertTrue(check_parity_cut_certificate(affine, cnf, derivation))
        self.assertIsNone(derivation["contradiction"])
        self.assertFalse(check_parity_cut_unsat_certificate(affine, cnf, derivation))
        envelope = {"kind": "parity-cuts-unsat-v1", "derivation": derivation, "residual": None}
        self.assertFalse(check_parity_cut_unsat_certificate(affine, cnf, envelope))
        # Removing a contradiction leaves sound cuts, but no final proof.
        impossible = AffineRelation(tuple("abcd"), ((7, 0),))
        proof = solve_with_parity_cuts(impossible, cnf, include_certificate=True)["certificate"]
        proof["derivation"]["contradiction"] = None
        self.assertTrue(check_parity_cut_certificate(impossible, cnf, proof["derivation"]))
        self.assertFalse(check_parity_cut_unsat_certificate(impossible, cnf, proof))
        # Check the other proof path and reject an incomplete residual scan.
        two = exactly_two(4)
        parity = AffineRelation(tuple("abcd"), ((15, 1),))
        fallback = solve_with_parity_cuts(parity, two, include_certificate=True)["certificate"]
        self.assertTrue(check_parity_cut_unsat_certificate(parity, two, fallback))
        fallback["residual"]["cells"].pop()
        self.assertFalse(check_parity_cut_unsat_certificate(parity, two, fallback))
        self.assertFalse(check_parity_cut_unsat_certificate(parity, two, None))

    def test_invalid_inputs_and_flags_are_rejected_before_short_circuit(self):
        affine = AffineRelation.truth(("a",))
        for cnf in (((0,),), ((2,),), ((-2,),), ((True,),), ((1.0,),),
                    ((1, -1, 2),), (1,), "a", ("",)):
            with self.assertRaises(ValueError):
                solve_with_parity_cuts(affine, cnf)
            with self.assertRaises(ValueError):
                derive_parity_cuts(affine, cnf)
        # Empty-clause UNSAT must not bypass validation of caller options.
        for cnf in ((), ((),)):
            for budget in (-1, 0.5, True):
                with self.assertRaises(ValueError):
                    solve_with_parity_cuts(affine, cnf, max_cells=budget)
            for flag in ("exhaustive", "include_trace", "include_certificate"):
                with self.assertRaises(ValueError):
                    solve_with_parity_cuts(affine, cnf, **{flag: 1})
        for proof in (None, [], {}, {"kind": "exactly-one-parity-cuts-v1"}):
            self.assertFalse(check_parity_cut_certificate(affine, (), proof))
        with self.assertRaises(ValueError):
            solve_with_parity_cuts(None, ())


if __name__ == "__main__":
    unittest.main()
