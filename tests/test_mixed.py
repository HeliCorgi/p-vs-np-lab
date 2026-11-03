"""Mixed solver checks against raw-equation finite semantics, never its compiler."""

from copy import deepcopy
from itertools import product
import json
import random
import unittest

from pnp_lab.affine import AffineRelation
from pnp_lab.mixed import check_sat_witness, check_unsat_certificate, solve_mixed


def brute_models(n, raw_rows, cnf):
    models = []
    for bits in product((0, 1), repeat=n):
        if not all(sum(bits[i] for i in range(n) if (mask >> i) & 1) % 2 == rhs
                   for mask, rhs in raw_rows):
            continue
        if not all(any(bits[abs(literal) - 1] == int(literal > 0) for literal in clause)
                   for clause in cnf):
            continue
        models.append(sum(bit << i for i, bit in enumerate(bits)))
    return set(models)


class MixedTests(unittest.TestCase):
    def test_random_formulas_against_raw_brute_force(self):
        rng = random.Random(8112026)
        satisfiable = unsatisfiable = 0
        for trial in range(180):
            n = rng.randrange(8)
            scope = tuple(f"v{i}" for i in range(n))
            source_witness = rng.randrange(1 << n)
            rows = tuple((mask, ((mask & source_witness).bit_count() % 2
                                 if trial % 3 else rng.randrange(2)))
                         for mask in (rng.randrange(1 << n) for _ in range(rng.randrange(n + 3))))
            clauses = []
            for _ in range(rng.randrange(8)):
                width = rng.randrange(5) if n else 0
                clauses.append(tuple(rng.choice((-1, 1)) * rng.randrange(1, n + 1) for _ in range(width)))
            cnf = tuple(clauses)
            affine = AffineRelation(scope, rows)
            expected = brute_models(n, rows, cnf)
            result = solve_mixed(affine, cnf, include_certificate=True)
            self.assertEqual(result["status"], "SAT" if expected else "UNSAT", (trial, rows, cnf))
            self.assertEqual(result["model_count"], len(expected), (trial, rows, cnf))
            self.assertTrue(result["exhaustive"])
            self.assertEqual(result["checked_cells"], result["satisfying_cells"] + result["rejecting_cells"])
            if expected:
                satisfiable += 1
                self.assertIn(result["witness_mask"], expected)
                self.assertTrue(check_sat_witness(affine, cnf, result["witness_mask"]))
                self.assertIsNone(result["certificate"])
            else:
                unsatisfiable += 1
                # Proof survives the actual JSON encoding used by the CLI.
                certificate = json.loads(json.dumps(result["certificate"]))
                self.assertTrue(check_unsat_certificate(affine, cnf, certificate), (trial, rows, cnf))
            if affine.is_consistent:
                d, r = result["affine_dimension"], result["effective_rank"]
                self.assertLessEqual(r, d)
                self.assertEqual(len(expected), result["satisfying_cells"] * (1 << (d - r)))
                self.assertEqual(len({cell["assignment_mask"] for cell in result["trace"]}), 1 << r)
        self.assertGreater(satisfiable, 20)
        self.assertGreater(unsatisfiable, 20)

    def test_observation_rank_lift_offsets_and_unused_directions(self):
        # x = 1 + a + b, y = a + b: two observed variables, only one form.
        scope = ("x", "y", "a", "b", "unused0", "unused1")
        rows = ((0b001101, 1), (0b001110, 0))
        affine = AffineRelation(scope, rows)
        cnf = ((1, 2),)
        result = solve_mixed(affine, cnf)
        self.assertEqual((result["affine_dimension"], result["effective_rank"]), (4, 1))
        self.assertEqual(result["checked_cells"], 2)
        self.assertEqual(result["model_count"], 16)
        self.assertEqual(result["omitted_affine_directions"], 3)
        self.assertTrue(all(cell["satisfies_cnf"] for cell in result["trace"]))
        for cell in result["trace"]:
            self.assertTrue(check_sat_witness(affine, cnf, cell["assignment_mask"]))
        # x and y have opposite offsets but the same non-coordinate form a+b.
        # Requiring both to be true rejects both fibers, including unused bits.
        impossible = ((1,), (2,))
        proof = solve_mixed(affine, impossible, include_certificate=True)
        self.assertEqual(proof["effective_rank"], 1)
        self.assertEqual(proof["certificate"]["observation_basis"], [3])
        self.assertTrue(check_unsat_certificate(affine, impossible, proof["certificate"]))
        self.assertEqual(brute_models(len(scope), rows, impossible), set())
        # Changing scope order changes DIMACS indices, not named semantics.
        reordered = affine.reorder(tuple(reversed(scope)))
        moved = solve_mixed(reordered, ((6, 5),))
        self.assertEqual(moved["model_count"], result["model_count"])
        self.assertEqual(moved["effective_rank"], 1)

    def test_empty_formulas_constants_tautologies_and_pure_cnf(self):
        self.assertEqual(solve_mixed(AffineRelation.truth(), ())["model_count"], 1)
        empty_unsat = solve_mixed(AffineRelation.truth(), ((),), include_certificate=True)
        self.assertEqual(empty_unsat["status"], "UNSAT")
        self.assertTrue(check_unsat_certificate(AffineRelation.truth(), ((),), empty_unsat["certificate"]))
        contradictory = solve_mixed(AffineRelation.false(), (), include_certificate=True)
        self.assertEqual(contradictory["checked_cells"], 0)
        self.assertIsNone(contradictory["effective_rank"])
        self.assertTrue(check_unsat_certificate(AffineRelation.false(), (), contradictory["certificate"]))
        scope = tuple("abcd")
        affine = AffineRelation.truth(scope)
        cnf = ((1, -1, 3), (2, 2), (2,))
        result = solve_mixed(affine, cnf)
        self.assertEqual(result["effective_rank"], 1)
        self.assertEqual(result["normalized_clause_count"], 1)
        self.assertEqual(result["model_count"], 8)
        self.assertEqual([cell["satisfied_clause_count"] for cell in result["trace"]], [1, 3])
        pinned = AffineRelation(scope, ((1, 1), (2, 0)))
        result = solve_mixed(pinned, ((1,), (-2,)))
        self.assertEqual(result["effective_rank"], 0)
        self.assertEqual(result["model_count"], 4)
        ordinary = solve_mixed(affine, ((1, 2, 3, 4),), include_trace=False)
        self.assertEqual(ordinary["effective_rank"], 4)
        self.assertEqual(ordinary["checked_cells"], 16)
        self.assertEqual(ordinary["model_count"], 15)

    def test_budgets_decision_mode_and_certificate_output_policy(self):
        affine = AffineRelation.truth(("a", "b", "c"))
        cnf = ((1,), (2,), (3,))
        partial = solve_mixed(affine, cnf, max_cells=7, include_certificate=True)
        self.assertEqual(partial["status"], "UNKNOWN")
        self.assertEqual(partial["checked_cells"], 7)
        self.assertIsNone(partial["model_count"])
        self.assertIsNone(partial["certificate"])
        self.assertEqual(solve_mixed(affine, cnf, max_cells=8)["status"], "SAT")
        zero = solve_mixed(affine, cnf, max_cells=0)
        self.assertEqual(zero["status"], "UNKNOWN")
        self.assertEqual(zero["checked_cells"], 0)
        early = solve_mixed(affine, ((-1, 2, 3),), exhaustive=False)
        self.assertEqual(early["status"], "SAT")
        self.assertEqual(early["checked_cells"], 1)
        self.assertFalse(early["exhaustive"])
        self.assertIsNone(early["model_count"])
        # Finding a witness with an incomplete budget is still a sound SAT result.
        partial_sat = solve_mixed(affine, ((-1, 2, 3),), max_cells=2)
        self.assertEqual(partial_sat["status"], "SAT")
        self.assertFalse(partial_sat["exhaustive"])
        self.assertIsNone(partial_sat["model_count"])
        unsat_cnf = ((1, 2), (-1,), (-2,))
        lean_output = solve_mixed(affine, unsat_cnf, include_trace=False)
        self.assertEqual(lean_output["trace"], [])
        self.assertIsNone(lean_output["certificate"])
        explicit_proof = solve_mixed(affine, unsat_cnf, include_trace=False, include_certificate=True)
        self.assertEqual(explicit_proof["trace"], [])
        self.assertEqual(len(explicit_proof["certificate"]["cells"]), 4)
        self.assertTrue(check_unsat_certificate(affine, unsat_cnf, explicit_proof["certificate"]))

    def test_unsat_certificate_rejects_incorrect_changes(self):
        affine = AffineRelation.truth(("a", "b", "unused"))
        cnf = ((1, 2), (-1,), (-2,))
        certificate = solve_mixed(affine, cnf, include_certificate=True)["certificate"]
        self.assertTrue(check_unsat_certificate(affine, cnf, certificate))
        mutations = []
        candidate = deepcopy(certificate)
        candidate["cells"].pop()
        mutations.append(candidate)
        candidate = deepcopy(certificate)
        candidate["cells"][1] = deepcopy(candidate["cells"][0])
        mutations.append(candidate)
        for key in ("free_assignment_mask", "assignment_mask", "satisfied_clause_count"):
            candidate = deepcopy(certificate)
            candidate["cells"][0][key] ^= 1
            mutations.append(candidate)
        for key in ("variable_forms", "observation_basis", "right_inverse"):
            candidate = deepcopy(certificate)
            candidate[key][0] = 0
            mutations.append(candidate)
        for key in ("affine_dimension", "effective_rank", "checked_cells", "rejecting_cells"):
            candidate = deepcopy(certificate)
            candidate[key] += 1
            mutations.append(candidate)
        candidate = deepcopy(certificate)
        candidate["satisfying_cells"] = 1
        mutations.append(candidate)
        candidate = deepcopy(certificate)
        candidate["cells"][0]["satisfies_cnf"] = True
        mutations.append(candidate)
        for candidate in mutations:
            self.assertFalse(check_unsat_certificate(affine, cnf, candidate))
        self.assertFalse(check_unsat_certificate(affine, (), certificate))
        self.assertFalse(check_unsat_certificate(affine, cnf, None))
        self.assertFalse(check_unsat_certificate(affine, cnf, {"kind": "inconsistent-affine-v1", "equation": [0, 1]}))

    def test_invalid_inputs_and_direct_witness_checker(self):
        affine = AffineRelation.truth(("a",))
        for cnf in (((0,),), ((2,),), ((-2,),), ((True,),), ((1.0,),), ((1, -1, 2),), (1,), "a", ("",)):
            with self.assertRaises(ValueError):
                solve_mixed(affine, cnf)
        for budget in (-1, 0.5, True):
            with self.assertRaises(ValueError):
                solve_mixed(affine, (), max_cells=budget)
        with self.assertRaises(ValueError):
            solve_mixed(affine, (), exhaustive=1)
        self.assertTrue(check_sat_witness(affine, ((1,),), 1))
        for witness in (0, -1, 2, None, True):
            self.assertFalse(check_sat_witness(affine, ((1,),), witness))
        self.assertFalse(check_sat_witness(AffineRelation(("a",), ((1, 0),)), ((1,),), 1))


if __name__ == "__main__":
    unittest.main()
