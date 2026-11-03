"""Independent Boolean semantics and adversarial checks for joint inference."""

from copy import deepcopy
import itertools
import json
import random
import unittest
from unittest.mock import patch

from pnp_lab.affine import AffineRelation
from pnp_lab.joint import (
    check_joint_clause_certificate,
    check_joint_unsat_certificate,
    derive_joint_clauses,
    solve_with_joint_reasoning,
)
from pnp_lab.mixed import solve_mixed
from pnp_lab.reductions import three_cnf_to_two_cnf_xor


def names(n):
    return tuple(f"x{i + 1}" for i in range(n))


def holds(cnf, values):
    return all(any(values[abs(lit) - 1] == int(lit > 0) for lit in clause)
               for clause in cnf)


def raw_models(n, rows, cnf):
    return {sum(value << j for j, value in enumerate(values))
            for values in itertools.product((0, 1), repeat=n)
            if all(sum(values[j] for j in range(n) if (mask >> j) & 1) % 2 == rhs
                   for mask, rhs in rows) and holds(cnf, values)}


def cycle(n):
    return tuple(clause for i in range(1, n + 1)
                 for clause in ((i, i % n + 1), (-i, -(i % n + 1))))


def exact_two(n):
    variables = tuple(range(1, n + 1))
    return (tuple(tuple(j for j in variables if i != j) for i in variables)
            + tuple(tuple(-j for j in triple) for triple in itertools.combinations(variables, 3)))


def parity_cnf(columns, rhs):
    clauses = []
    for forbidden in itertools.product((0, 1), repeat=len(columns)):
        if sum(forbidden) % 2 != rhs:
            clauses.append(tuple(-(column + 1) if value else column + 1
                                 for column, value in zip(columns, forbidden)))
    return tuple(clauses)


class JointReasoningTests(unittest.TestCase):
    def test_all_signed_forcing_patterns_through_width_three(self):
        checked = 0
        for width in range(1, 4):
            for pivot_signs in itertools.product((-1, 1), repeat=width):
                for partner_signs in itertools.product((-1, 1), repeat=width):
                    for rhs in (0, 1):
                        n = 2 * width
                        rows = (((1 << width) - 1, rhs),)
                        cnf = tuple((pivot_signs[i] * (i + 1),
                                     partner_signs[i] * (width + i + 1)) for i in range(width))
                        affine = AffineRelation(names(n), rows)
                        proof = derive_joint_clauses(affine, cnf)
                        self.assertTrue(check_joint_clause_certificate(affine, cnf, proof))
                        mismatch = sum(sign > 0 for sign in pivot_signs) % 2 != rhs
                        self.assertEqual(len(proof["clauses"]), int(mismatch))
                        augmented = cnf + tuple(tuple(step["clause"]) for step in proof["clauses"])
                        self.assertEqual(raw_models(n, rows, cnf), raw_models(n, rows, augmented))
                        checked += 1
        self.assertEqual(checked, 168)

    def test_shared_partners_tautologies_and_reused_binary_premises(self):
        affine = AffineRelation(names(4), ((7, 0),))
        cnf = ((1, 4, 4), (2, 4), (3, 4), (1, -1))
        proof = derive_joint_clauses(affine, cnf)
        self.assertEqual([step["clause"] for step in proof["clauses"]], [[4]])
        self.assertTrue(check_joint_clause_certificate(affine, cnf, proof))
        result = solve_with_joint_reasoning(affine, cnf, exhaustive=True, include_trace=False)
        self.assertEqual(result["model_count"], len(raw_models(4, ((7, 0),), cnf)))
        tautological = ((1, 4), (2, -4), (3, 4))
        self.assertEqual(derive_joint_clauses(affine, tautological)["clauses"], [])

        # One clause may legitimately serve different row coordinates. The
        # finder skips this already-present conclusion, but its proof is sound.
        affine = AffineRelation(names(2), ((3, 1),))
        cnf = ((1, 2),)
        proof = derive_joint_clauses(affine, cnf)
        proof["clauses"] = [{"xor_row": 0,
                             "premises": [{"pivot_literal": 1, "clause": 0},
                                          {"pivot_literal": 2, "clause": 0}],
                             "clause": [1, 2]}]
        self.assertTrue(check_joint_clause_certificate(affine, cnf, proof))

    def test_bridge_odd_cycles_are_refuted_before_enumeration(self):
        for n in (3, 5, 9):
            source = cycle(n)
            bridge = three_cnf_to_two_cnf_xor(names(n), source)
            result = solve_with_joint_reasoning(bridge.affine, bridge.cnf, exhaustive=False,
                                                max_cells=0, include_trace=False,
                                                include_certificate=True)
            joint = result["joint_preprocessing"]
            self.assertEqual(joint["derived_clause_count"], 2 * n)
            self.assertEqual({tuple(step["clause"]) for step in joint["derivation"]["clauses"]},
                             {tuple(sorted(clause, key=lambda lit: (abs(lit), lit))) for clause in source})
            self.assertEqual(result["status"], "UNSAT")
            self.assertEqual(result["checked_cells"], 0)
            self.assertTrue(joint["certificate_checked"])
            self.assertTrue(check_joint_unsat_certificate(bridge.affine, bridge.cnf,
                                                          result["certificate"]))

    def test_sat_model_counts_are_target_counts_not_source_counts(self):
        bridge = three_cnf_to_two_cnf_xor(names(3), ((1, 2, 3),))
        result = solve_with_joint_reasoning(bridge.affine, bridge.cnf, exhaustive=True,
                                            include_trace=False)
        original = raw_models(6, bridge.affine.equations, bridge.cnf)
        self.assertEqual(len(original), 13)
        self.assertEqual(result["model_count"], 13)
        self.assertIn(result["witness_mask"], original)
        # The source has seven models; the bridge itself is not parsimonious.
        self.assertEqual(len(raw_models(3, (), ((1, 2, 3),))), 7)

    def test_corrupt_joint_and_composed_proofs_are_rejected(self):
        affine = AffineRelation(names(4), ((3, 0),))
        cnf = ((1, 3), (-2, 4))
        valid = derive_joint_clauses(affine, cnf)
        self.assertEqual(valid["clauses"][0]["clause"], [3, 4])
        corruptions = []
        bad = deepcopy(valid); bad["max_row_width"] = 4; corruptions.append(bad)
        bad = deepcopy(valid); bad["candidates_examined"] = True; corruptions.append(bad)
        bad = deepcopy(valid); bad["candidates_examined"] = 0; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["xor_row"] = -1; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["xor_row"] = False; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["premises"].pop(); corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["premises"][0]["pivot_literal"] = -1; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["premises"][1]["clause"] = 0; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["clause"] = [3, -4]; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["clause"] = [3, 3, 4]; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"][0]["clause"] = [0]; corruptions.append(bad)
        bad = deepcopy(valid); bad["clauses"].append(deepcopy(bad["clauses"][0])); corruptions.append(bad)
        for bad in corruptions:
            self.assertFalse(check_joint_clause_certificate(affine, cnf, bad))
        self.assertTrue(check_joint_clause_certificate(affine, cnf, json.loads(json.dumps(valid))))

        bridge = three_cnf_to_two_cnf_xor(names(3), cycle(3))
        result = solve_with_joint_reasoning(bridge.affine, bridge.cnf, max_cells=0,
                                            include_trace=False, include_certificate=True)
        proof = result["certificate"]
        self.assertTrue(check_joint_unsat_certificate(bridge.affine, bridge.cnf,
                                                      json.loads(json.dumps(proof))))
        bad = deepcopy(proof); bad["joint_derivation"]["clauses"][0]["clause"] = []
        self.assertFalse(check_joint_unsat_certificate(bridge.affine, bridge.cnf, bad))
        bad = deepcopy(proof); bad["residual"] = None
        self.assertFalse(check_joint_unsat_certificate(bridge.affine, bridge.cnf, bad))

    def test_checker_does_not_call_finders_solvers_or_gaussian_elimination(self):
        bridge = three_cnf_to_two_cnf_xor(names(3), cycle(3))
        result = solve_with_joint_reasoning(bridge.affine, bridge.cnf, max_cells=0,
                                            include_trace=False, include_certificate=True)
        def forbidden(*args, **kwargs):
            raise AssertionError("Producer or Gaussian elimination entered checker path")
        with (patch("pnp_lab.joint.derive_joint_clauses", forbidden),
              patch("pnp_lab.joint.solve_with_joint_reasoning", forbidden),
              patch("pnp_lab.joint.solve_with_parity_cuts", forbidden),
              patch("pnp_lab.joint._normalize_cnf", forbidden),
              patch("pnp_lab.joint._support", forbidden),
              patch("pnp_lab.parity_cuts.derive_parity_cuts", forbidden),
              patch("pnp_lab.parity_cuts._normalize_cnf", forbidden),
              patch("pnp_lab.parity_cuts.solve_mixed", forbidden),
              patch("pnp_lab.affine._rref", forbidden)):
            self.assertTrue(check_joint_clause_certificate(
                bridge.affine, bridge.cnf, result["joint_preprocessing"]["derivation"]))
            self.assertTrue(check_joint_unsat_certificate(bridge.affine, bridge.cnf,
                                                          result["certificate"]))

    def test_fixed_width_limit_and_exact_two_barrier(self):
        affine = AffineRelation(names(5), ((15, 1),))
        cnf = ((1, 5), (2, 5), (3, 5), (4, 5))
        proof = derive_joint_clauses(affine, cnf)
        self.assertEqual(proof["candidates_examined"], 0)
        self.assertEqual(proof["clauses"], [])
        for n in (4, 5, 6):
            affine = AffineRelation(names(n), (((1 << n) - 1, 1),))
            cnf = exact_two(n)
            result = solve_with_joint_reasoning(affine, cnf, exhaustive=False,
                                                include_trace=False, include_certificate=True)
            self.assertEqual(result["joint_preprocessing"]["derived_clause_count"], 0)
            self.assertEqual(result["preprocessing"]["derived_cut_count"], 0)
            self.assertEqual(result["status"], "UNSAT")
            self.assertEqual(result["checked_cells"], 1 << (n - 1))
            self.assertTrue(check_joint_unsat_certificate(affine, cnf, result["certificate"]))
            limited = solve_with_joint_reasoning(affine, cnf, max_cells=0, include_trace=False)
            self.assertEqual(limited["status"], "UNKNOWN")
            self.assertIsNone(limited["certificate"])

    def test_connected_ternary_tseitin_barrier_has_no_binary_premises(self):
        # Prism graph: upper cycle a_i, lower cycle b_i, rungs r_i.
        # Only upper vertex0 has odd charge and a native XOR; all other
        # vertex equations are represented by four width-three clauses.
        for k in (3, 4):
            n = 3 * k
            vertices = [(i, (i - 1) % k, 2 * k + i) for i in range(k)]
            vertices += [(k + i, k + (i - 1) % k, 2 * k + i) for i in range(k)]
            row = (sum(1 << column for column in vertices[0]), 1)
            cnf = sum((parity_cnf(columns, 0) for columns in vertices[1:]), ())
            self.assertTrue(all(len(clause) == 3 for clause in cnf))
            self.assertTrue(raw_models(n, (), cnf))
            self.assertTrue(raw_models(n, (row,), ()))
            self.assertFalse(raw_models(n, (row,), cnf))
            affine = AffineRelation(names(n), (row,))
            result = solve_with_joint_reasoning(affine, cnf, exhaustive=False, include_trace=False)
            self.assertEqual(result["joint_preprocessing"]["candidates_examined"], 0)
            self.assertEqual(result["preprocessing"]["derived_cut_count"], 0)
            self.assertEqual(result["status"], "UNSAT")
            self.assertEqual(result["checked_cells"], 1 << (n - 1))
            self.assertEqual(result["effective_rank"], n - 1)

    def test_empty_rows_empty_clauses_and_invalid_budgets(self):
        false = AffineRelation.false(())
        proof = derive_joint_clauses(false, ())
        self.assertEqual(proof["clauses"], [{"xor_row": 0, "premises": [], "clause": []}])
        self.assertTrue(check_joint_clause_certificate(false, (), proof))
        result = solve_with_joint_reasoning(false, (), max_cells=0, include_certificate=True)
        self.assertEqual(result["status"], "UNSAT")
        self.assertTrue(check_joint_unsat_certificate(false, (), result["certificate"]))
        truth = AffineRelation.truth(())
        self.assertEqual(solve_with_joint_reasoning(truth, (), include_trace=False)["model_count"], 1)
        empty = solve_with_joint_reasoning(truth, ((),), max_cells=0, include_certificate=True)
        self.assertEqual(empty["status"], "UNSAT")
        self.assertTrue(check_joint_unsat_certificate(truth, ((),), empty["certificate"]))
        for budget in (-1, True, 0.5):
            with self.assertRaises(ValueError):
                solve_with_joint_reasoning(false, (), max_cells=budget)
        for field in ("exhaustive", "include_trace", "include_certificate"):
            with self.assertRaises(ValueError):
                solve_with_joint_reasoning(false, (), **{field: 1})
        with self.assertRaises(ValueError):
            derive_joint_clauses(AffineRelation.truth(names(1)), ((0,),))
        self.assertFalse(check_joint_clause_certificate(truth, (), None))
        self.assertFalse(check_joint_unsat_certificate(truth, (), None))

    def test_fixed_seed_raw_original_input_oracle(self):
        rng = random.Random(2026110404)
        for case in range(160):
            n = 1 + case % 7
            rows = tuple((rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(4)))
            cnf = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                              for _ in range(rng.randrange(5))) for _ in range(rng.randrange(7)))
            if n >= 2 and case % 2 == 0:
                width = min(3, n - 1)
                rows += (((1 << width) - 1, rng.randrange(2)),)
                cnf += tuple((rng.choice((-1, 1)) * (i + 1),
                              rng.choice((-1, 1)) * rng.randint(width + 1, n)) for i in range(width))
            models = raw_models(n, rows, cnf)
            affine = AffineRelation(names(n), rows)
            result = solve_with_joint_reasoning(affine, cnf, exhaustive=True,
                                                include_trace=False, include_certificate=True)
            self.assertEqual(result["model_count"], len(models), case)
            self.assertEqual(result["status"], "SAT" if models else "UNSAT", case)
            baseline = solve_mixed(affine, cnf, exhaustive=True, include_trace=False)
            self.assertEqual(baseline["model_count"], len(models), case)
            derivation = result["joint_preprocessing"]["derivation"]
            self.assertTrue(check_joint_clause_certificate(affine, cnf, derivation), case)
            augmented = cnf + tuple(tuple(step["clause"]) for step in derivation["clauses"])
            self.assertEqual(raw_models(n, rows, augmented), models, case)
            if models:
                self.assertIn(result["witness_mask"], models, case)
            else:
                self.assertTrue(check_joint_unsat_certificate(affine, cnf, result["certificate"]), case)


if __name__ == "__main__":
    unittest.main()
