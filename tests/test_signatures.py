"""Compare exact signature counts with independent ORIGINAL-input semantics."""

from itertools import combinations, permutations, product
import json
import random
import unittest

from pnp_lab.affine import AffineRelation
from pnp_lab.signatures import count_by_signatures


def original_models(n, raw_rows, raw_cnf):
    """No RREF, clause normalization, group tables, or solver helper calls."""
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
    return (literals,) + tuple((-a, -b) for a, b in combinations(literals, 2))


class SignatureCountingTests(unittest.TestCase):
    def assert_models(self, result, affine, expected):
        self.assertEqual(result["status"], "SAT" if expected else "UNSAT")
        self.assertEqual(result["model_count"], len(expected))
        self.assertTrue(result["exhaustive"])
        self.assertEqual(result["group_assignments_tested"],
                         sum(result["group_assignments_tested_by_group"]))
        self.assertEqual(result["join_products"], sum(result["join_products_by_group"]))
        if expected:
            self.assertIn(result["witness_mask"], expected)
            self.assertEqual(result["witness"], {
                name: (result["witness_mask"] >> i) & 1 for i, name in enumerate(affine.variables)
            })
        else:
            self.assertIsNone(result["witness"])
            self.assertIsNone(result["witness_mask"])
        self.assertEqual(json.loads(json.dumps(result)), result)

    def test_fixed_seed_local_formulas_match_raw_exhaustive_oracle(self):
        rng = random.Random(2026110307)
        sat = unsat = 0
        for trial in range(198):
            n = trial % 9
            names = tuple(f"v{i}" for i in range(n))
            order = list(range(n))
            rng.shuffle(order)
            groups = []
            while order:
                size = rng.randrange(1, min(4, len(order)) + 1)
                groups.append(tuple(names[i] for i in order[:size]))
                del order[:size]
            planted = rng.randrange(1 << n)
            raw_rows = tuple((mask, ((mask & planted).bit_count() & 1)
                              if trial % 2 else rng.randrange(2))
                             for mask in (rng.randrange(1 << n)
                                          for _ in range(rng.randrange(n + 2))))
            clauses = []
            for group in groups:
                variables = [names.index(name) + 1 for name in group]
                for _ in range(rng.randrange(5)):
                    clause = [rng.choice((-1, 1)) * rng.choice(variables)
                              for _ in range(rng.randrange(1, 5))]
                    if trial % 2 and not any(((planted >> (abs(lit) - 1)) & 1) == (lit > 0)
                                             for lit in clause):
                        clause[0] = abs(clause[0]) * (1 if (planted >> (abs(clause[0]) - 1)) & 1 else -1)
                    clauses.append(tuple(clause))
            if n:
                # A tautology can span groups and must disappear before the
                # support restriction; all its literals are still validated.
                clauses.append((1, -1, n))
            if clauses and trial % 3 == 0:
                clauses.append(clauses[0])
            if trial % 19 == 0:
                clauses.append(())
            raw_cnf = tuple(clauses)
            affine = AffineRelation(names, raw_rows)
            expected = original_models(n, raw_rows, raw_cnf)
            result = count_by_signatures(affine, (iter(c) for c in raw_cnf),
                                         (iter(group) for group in groups))
            with self.subTest(trial=trial, n=n):
                self.assert_models(result, affine, expected)
            sat += bool(expected)
            unsat += not expected
        self.assertGreater(sat, 65)
        self.assertGreater(unsat, 45)

    def test_group_order_and_variable_order_permutations(self):
        names = ("a", "b", "c", "d", "e", "f")
        raw_rows = ((0b010101, 0), (0b101010, 1), (0b111111, 1))
        cnf = ((1, -2), (-3, 4), (5, 6), (-5, -6), (1, 1, -2))
        affine = AffineRelation(names, raw_rows)
        expected = original_models(6, raw_rows, cnf)
        self.assertTrue(expected)
        for ordered in permutations((("a", "b"), ("c", "d"), ("e", "f"))):
            for reversals in product((False, True), repeat=3):
                groups = [tuple(reversed(group)) if reverse else group
                          for group, reverse in zip(ordered, reversals)]
                result = count_by_signatures(affine, cnf, groups)
                self.assert_models(result, affine, expected)
                self.assertEqual(result["group_assignments_tested"], 12)

    def test_exact_multiplicity_and_explicit_free_variables(self):
        names = tuple(f"x{i}" for i in range(8))
        cnf = exactly_one((1, 2, 3)) + exactly_one((4, 5, 6))
        rows = ((0b111111, 0),)
        affine = AffineRelation(names, rows)
        groups = (names[:3], names[3:6], names[6:])
        result = count_by_signatures(affine, cnf, groups)
        self.assert_models(result, affine, original_models(8, rows, cnf))
        self.assertEqual(result["model_count"], 36)
        self.assertEqual(result["group_valid_assignment_counts"], [3, 3, 4])
        self.assertEqual(result["group_signature_counts"], [1, 1, 1])
        self.assertEqual(result["group_assignments_tested"], 20)
        self.assertEqual(result["join_products"], 3)
        self.assertEqual(result["dp_state_counts"], [1, 1, 1, 1])

    def test_two_bit_signatures_and_colliding_join_products(self):
        names = tuple(f"x{i}" for i in range(6))
        cnf = exactly_one((1, 2, 3)) + exactly_one((4, 5, 6))
        for right_a, right_b in product((0, 1), repeat=2):
            rows = ((0b001001, right_a), (0b010010, right_b))
            affine = AffineRelation(names, rows)
            result = count_by_signatures(affine, cnf, (names[:3], names[3:]))
            self.assert_models(result, affine, original_models(6, rows, cnf))
            self.assertEqual(result["signature_bits"], 2)
            self.assertEqual(result["group_signature_counts"], [3, 3])
            self.assertEqual(result["dp_state_counts"], [1, 3, 4])
            self.assertEqual(result["join_products_by_group"], [3, 9])
            self.assertEqual(result["model_count"], 3 if right_a == right_b == 0 else 2)

    def test_identity_measurements_make_explicit_tables_exponential(self):
        for n in range(1, 9):
            names = tuple(f"x{i}" for i in range(n))
            rows = tuple((1 << i, 0) for i in range(n))
            affine = AffineRelation(names, rows)
            result = count_by_signatures(affine, (), (names,))
            self.assert_models(result, affine, original_models(n, rows, ()))
            self.assertEqual(result["model_count"], 1)
            self.assertEqual(result["witness_mask"], 0)
            self.assertEqual(result["group_signature_counts"], [1 << n])
            self.assertEqual(result["dp_state_counts"], [1, 1 << n])
            self.assertEqual(result["join_products"], 1 << n)

    def test_whole_scope_group_accepts_general_signed_cnf(self):
        names = tuple("abcdefgh")
        rows = ((0b10101010, 1), (0b11110000, 0))
        cnf = ((1, 3, -8), (-2, -4, 7), (2, 5), (-6, 8), (1, -1))
        affine = AffineRelation(names, rows)
        result = count_by_signatures(affine, cnf, (tuple(reversed(names)),))
        self.assert_models(result, affine, original_models(8, rows, cnf))
        self.assertEqual(result["group_assignments_tested"], 256)

    def test_empty_scope_empty_groups_and_immediate_contradictions(self):
        truth = AffineRelation.truth()
        result = count_by_signatures(truth, (), (), max_group_assignments=0, max_join_products=0)
        self.assert_models(result, truth, {0})
        self.assertEqual(result["witness"], {})
        self.assertEqual(result["group_assignments_tested"], 0)
        self.assertEqual(result["join_products"], 0)
        with_empty = count_by_signatures(truth, (), ((),), max_group_assignments=1, max_join_products=1)
        self.assert_models(with_empty, truth, {0})
        self.assertEqual(with_empty["group_assignments_tested"], 1)
        self.assertEqual(with_empty["group_signature_counts"], [1])
        self.assertEqual(count_by_signatures(truth, (), ((),), max_group_assignments=0)["status"], "UNKNOWN")
        for affine, cnf, groups, reason in ((truth, ((),), (), "empty_cnf_clause"),
                                          (AffineRelation.false(), (), (), "inconsistent_xor"),
                                          (AffineRelation.false(("x",)), (), (("x",),), "inconsistent_xor")):
            result = count_by_signatures(affine, cnf, groups,
                                         max_group_assignments=0, max_join_products=0)
            self.assert_models(result, affine, set())
            self.assertEqual(result["reason"], reason)
            self.assertEqual(result["group_assignments_tested"], 0)

    def test_assignment_budget_total_exact_boundary_and_partial_table(self):
        affine = AffineRelation.truth(("a", "b"))
        groups = (("a",), ("b",))
        for budget in range(4):
            result = count_by_signatures(affine, (), groups, max_group_assignments=budget)
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertEqual(result["reason"], "group_assignment_budget_exhausted")
            self.assertEqual(result["group_assignments_tested"], budget)
            self.assertFalse(result["exhaustive"])
            self.assertIsNone(result["model_count"])
            self.assertIsNone(result["witness"])
        partial = count_by_signatures(affine, (), groups, max_group_assignments=3)
        self.assertEqual(partial["group_tables_complete"], [True, False])
        self.assertEqual(partial["group_signature_counts"], [1, 1])
        self.assertEqual(partial["group_valid_assignment_counts"], [2, 1])
        full = count_by_signatures(affine, (), groups, max_group_assignments=4, max_join_products=2)
        self.assert_models(full, affine, {0, 1, 2, 3})

    def test_join_budget_never_claims_sat_from_a_partial_sum(self):
        affine = AffineRelation(("a", "b"), ((1, 0), (2, 0)))
        groups = (("a",), ("b",))
        # First join has 2 products; the second has 4. The desired zero
        # signature already occurs before completion, but its count is not
        # certified by an interrupted convolution.
        for budget in range(6):
            result = count_by_signatures(affine, (), groups, max_join_products=budget)
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertEqual(result["join_products"], budget)
            self.assertEqual(result["reason"], "join_product_budget_exhausted")
            self.assertIsNone(result["model_count"])
            self.assertIsNone(result["witness"])
            self.assertEqual(result["group_tables_complete"], [True, True])
        partial = count_by_signatures(affine, (), groups, max_join_products=3)
        self.assertEqual(partial["dp_state_counts"], [1, 2])
        self.assertEqual(partial["join_products_by_group"], [2, 1])
        self.assertEqual(partial["join_partial_group_index"], 1)
        self.assertEqual(partial["join_partial_state_count"], 1)
        full = count_by_signatures(affine, (), groups, max_join_products=6)
        self.assert_models(full, affine, {0})

    def test_a_completed_empty_local_table_proves_zero_without_join(self):
        affine = AffineRelation.truth(("a", "b"))
        result = count_by_signatures(affine, ((1,), (-1,)), (("a",), ("b",)),
                                     max_group_assignments=2, max_join_products=0)
        self.assert_models(result, affine, set())
        self.assertEqual(result["reason"], "group_cnf_unsatisfiable")
        self.assertEqual(result["group_tables_complete"], [True, False])
        self.assertEqual(result["group_assignments_tested_by_group"], [2, 0])

    def test_cross_group_clauses_rejected_after_tautology_normalization(self):
        affine = AffineRelation.truth(("a", "b"))
        groups = (("a",), ("b",))
        for cnf in (((1, 2),), ((1, -2),), ((), (1, 2))):
            with self.assertRaisesRegex(ValueError, "cross-group"):
                count_by_signatures(affine, cnf, groups)
        with self.assertRaisesRegex(ValueError, "cross-group"):
            count_by_signatures(AffineRelation.false(("a", "b")), ((1, 2),), groups)
        result = count_by_signatures(affine, ((1, -1, 2), (1, 1), (1,)), groups)
        self.assert_models(result, affine, {1, 3})
        self.assertEqual(result["normalized_clause_count"], 1)
        with self.assertRaises(ValueError):
            count_by_signatures(affine, ((1, -1, 3),), groups)

    def test_validation_rejects_malformed_partitions_and_budgets(self):
        affine = AffineRelation.truth(("a", "b"))
        for groups in (None, "ab", ("ab",), (("a",),), (("a", "a"), ("b",)),
                       (("a",), ("a", "b")), (("a", "c"),), ((["a"], "b"),), (1,)):
            with self.subTest(groups=groups), self.assertRaises(ValueError):
                count_by_signatures(affine, (), groups)
        for key in ("max_group_assignments", "max_join_products"):
            for budget in (-1, True, 1.0, "1"):
                with self.subTest(key=key, budget=budget), self.assertRaises(ValueError):
                    count_by_signatures(affine, (), (("a", "b"),), **{key: budget})
        for cnf in (None, "x", ("a",), ((True,),), ((0,),), ((3,),)):
            with self.subTest(cnf=cnf), self.assertRaises(ValueError):
                count_by_signatures(affine, cnf, (("a", "b"),))
        with self.assertRaises(ValueError):
            count_by_signatures(None, (), ())


if __name__ == "__main__":
    unittest.main()
