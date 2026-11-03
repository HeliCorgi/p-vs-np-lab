"""Independent Boolean and structural checks for the constant-block bridge."""

from collections import Counter
import itertools
import random
import unittest

from pnp_lab.block_bridge import three_cnf_to_constant_blocks
from pnp_lab.signatures import count_by_signatures


def raw_cnf(clauses, values):
    return all(any(values[abs(literal) - 1] == int(literal > 0) for literal in clause)
               for clause in clauses)


def values_of(mask, width):
    return tuple((mask >> i) & 1 for i in range(width))


def raw_target(reduction, mask):
    values = values_of(mask, len(reduction.bridge.affine.variables))
    return (raw_cnf(reduction.bridge.cnf, values)
            and all(sum(values[i] for i in range(len(values)) if row & (1 << i)) % 2 == rhs
                    for row, rhs in reduction.bridge.affine.equations))


class ConstantBlockBridgeTests(unittest.TestCase):
    def assert_shape(self, reduction):
        bridge = reduction.bridge
        names = bridge.affine.variables
        self.assertEqual(len(names), len(set(names)))
        flattened = tuple(name for group in reduction.groups for name in group)
        self.assertEqual(len(flattened), len(set(flattened)))
        self.assertEqual(set(flattened), set(names))
        self.assertTrue(all(1 <= len(group) <= 5 for group in reduction.groups))
        owner = {name: index for index, group in enumerate(reduction.groups) for name in group}
        for clause in bridge.cnf:
            if clause:
                self.assertEqual(len(clause), 2)
                self.assertEqual(len({owner[names[abs(literal) - 1]] for literal in clause}), 1)
        used = 0
        for row, rhs in bridge.affine.equations:
            self.assertEqual(row.bit_count(), 3)
            self.assertEqual(rhs, 0)
            self.assertEqual(used & row, 0)
            used |= row
        if any(not clause for clause in reduction.original_cnf):
            self.assertEqual(names, ())
            self.assertEqual(bridge.cnf, ((),))
            self.assertEqual(reduction.groups, ())
        else:
            m = len(reduction.original_cnf)
            self.assertEqual(len(reduction.groups), 3 * m)
            self.assertLessEqual(len(bridge.affine.equations), 4 * m)
            self.assertLessEqual(len(names), 15 * m)
            self.assertTrue(all(len(clause) == 3 for clause in reduction.expanded_cnf))
            self.assertEqual(bridge.original_variables, reduction.copy_variables)
            self.assertEqual(bridge.original_cnf, reduction.expanded_cnf)
            frequency = Counter(reduction.copy_to_original)
            for copy, group in enumerate(reduction.groups):
                self.assertEqual(group[0], reduction.copy_variables[copy])
                self.assertEqual(len(group), 5 if frequency[reduction.copy_to_original[copy]] > 1 else 2)

    def assert_matches_source_oracle(self, variables, clauses):
        reduction = three_cnf_to_constant_blocks(variables, clauses)
        self.assert_shape(reduction)
        source_models = {mask for mask in range(1 << len(variables))
                         if raw_cnf(clauses, values_of(mask, len(variables)))}
        counted = count_by_signatures(reduction.bridge.affine, reduction.bridge.cnf, reduction.groups)
        self.assertEqual(counted["status"], "SAT" if source_models else "UNSAT")
        self.assertTrue(counted["exhaustive"])
        self.assertLessEqual(max(counted["group_signature_counts"], default=0), 5)
        active_mask = sum(1 << original for original in set(reduction.copy_to_original))
        for original in range(1 << len(variables)):
            if original in source_models:
                target = reduction.lift_witness(original)
                self.assertTrue(raw_target(reduction, target))
                self.assertEqual(reduction.project_witness(target), original & active_mask)
            else:
                with self.assertRaises(ValueError):
                    reduction.lift_witness(original)
        if source_models:
            target = counted["witness_mask"]
            self.assertTrue(raw_target(reduction, target))
            self.assertIn(reduction.project_witness(target), source_models)
        return reduction, counted

    def test_all_target_assignments_for_one_distinct_signed_clause(self):
        for clause in ((1, 2, 3), (-1, 2, -3)):
            reduction = three_cnf_to_constant_blocks(("a", "b", "c"), (clause,))
            projected = set()
            model_count = 0
            for target in range(1 << len(reduction.bridge.affine.variables)):
                if raw_target(reduction, target):
                    model_count += 1
                    projected.add(reduction.project_witness(target))
                else:
                    with self.assertRaises(ValueError):
                        reduction.project_witness(target)
            expected = {mask for mask in range(8) if raw_cnf((clause,), values_of(mask, 3))}
            self.assertEqual(projected, expected)
            self.assertEqual(model_count, 13)
            self.assertEqual(len(expected), 7)

    def test_fixed_seed_small_source_oracles(self):
        rng = random.Random(681247)
        for case in range(40):
            n = rng.randint(1, 4)
            clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                                  for _ in range(rng.randint(1, 3)))
                            for _ in range(rng.randint(0, 2)))
            with self.subTest(case=case, clauses=clauses):
                self.assert_matches_source_oracle(tuple(f"x{i}" for i in range(n)), clauses)

    def test_short_signed_repeated_tautological_and_unsat_sources(self):
        for clauses in (((1,),), ((-1,),), ((1, -2),), ((1, 1, -2),),
                        ((1, -1, 2),), ((1,), (-1,)), ((1, 2), (-1, -2))):
            with self.subTest(clauses=clauses):
                self.assert_matches_source_oracle(("x", "y"), clauses)

    def test_padding_precedes_copying_and_cycles_enforce_equality(self):
        reduction = three_cnf_to_constant_blocks(("x", "y"), ((1,), (-1, 2)))
        self.assertEqual(reduction.copy_to_original, (0, 0, 0, 0, 1, 1))
        self.assertEqual(reduction.expanded_cnf[:2], ((1, 2, 3), (-4, 5, 6)))
        self.assertEqual(reduction.expanded_cnf[2:],
                         ((-1, 2, 2), (-2, 3, 3), (-3, 4, 4), (-4, 1, 1),
                          (-5, 6, 6), (-6, 5, 5)))
        for copied in itertools.product((0, 1), repeat=6):
            equal = all(len({copied[i] for i, source in enumerate(reduction.copy_to_original)
                             if source == original}) == 1 for original in (0, 1))
            self.assertEqual(raw_cnf(reduction.expanded_cnf[2:], copied), equal)

    def test_local_signature_supports_and_assignment_counts(self):
        for sign, expected_valid in ((1, 10), (-1, 8)):
            reduction, counted = self.assert_matches_source_oracle(("x",), ((sign,),))
            self.assertEqual([len(group) for group in reduction.groups], [5, 5, 5])
            self.assertEqual(counted["group_signature_counts"], [5, 5, 5])
            self.assertEqual(counted["group_valid_assignment_counts"], [expected_valid] * 3)
        _, counted = self.assert_matches_source_oracle(("x", "y", "z"), ((1, -2, 3),))
        self.assertEqual(counted["group_signature_counts"], [2, 2, 2])

    def test_disjoint_positive_triples_work_formulas(self):
        for m in range(1, 7):
            reduction = three_cnf_to_constant_blocks(
                tuple(f"x{i}" for i in range(3 * m)),
                tuple((3 * i + 1, 3 * i + 2, 3 * i + 3) for i in range(m)))
            self.assert_shape(reduction)
            counted = count_by_signatures(reduction.bridge.affine, reduction.bridge.cnf, reduction.groups)
            self.assertEqual(counted["group_sizes"], [2] * (3 * m))
            self.assertEqual(counted["model_count"], 13 ** m)
            self.assertEqual(counted["group_assignments_tested"], 12 * m)
            self.assertEqual(counted["dp_states_peak"], 2 ** m)
            self.assertEqual(counted["join_products"], 10 * (2 ** m - 1))

    def test_empty_inputs_and_unused_explicit_scope(self):
        for variables, clauses in (((), ()), (("unused",), ()), ((), ((),)),
                                   (("unused",), ((),)), (("x", "unused"), ((1,), ()) )):
            with self.subTest(variables=variables, clauses=clauses):
                reduction, _ = self.assert_matches_source_oracle(variables, clauses)
                self.assertEqual(reduction.original_variables, variables)
                self.assertEqual(reduction.original_cnf, clauses)
        reduction, _ = self.assert_matches_source_oracle(("unused", "x", "unused2"), ((2,),))
        for mask in (2, 3, 6, 7):
            self.assertEqual(reduction.project_witness(reduction.lift_witness(mask)), 2)

    def test_fresh_copy_names_and_snapshot_metadata(self):
        variables = ["__pnp_occurrence_0_0", "__pnp_occurrence_0_0_", "x"]
        clauses = [[1, -2, 3]]
        reduction = three_cnf_to_constant_blocks(variables, clauses)
        self.assertTrue(set(reduction.copy_variables).isdisjoint(variables))
        self.assertEqual(reduction.copy_variables[0], "__pnp_occurrence_0_0__")
        self.assert_shape(reduction)
        variables.append("later")
        clauses[0][0] = -1
        self.assertEqual(len(reduction.original_variables), 3)
        self.assertEqual(reduction.original_cnf, ((1, -2, 3),))

    def test_invalid_inputs_are_validated_before_empty_clause_shortcut(self):
        for bad in ((0,), (2,), (True,), (1.0,), ("1",), (1, 1, 1, 1)):
            for clauses in ((bad,), ((), bad), (bad, ())):
                with self.subTest(clauses=clauses), self.assertRaises(ValueError):
                    three_cnf_to_constant_blocks(("x",), clauses)
        for variables in (("x", "x"), ("",), (None,), (1,)):
            with self.subTest(variables=variables), self.assertRaises(ValueError):
                three_cnf_to_constant_blocks(variables, ((),))
        reduction = three_cnf_to_constant_blocks(("x",), ((1,),))
        for mask in (-1, 2, True, 0.0, None):
            with self.subTest(source_mask=mask), self.assertRaises(ValueError):
                reduction.lift_witness(mask)
        for mask in (-1, 1 << len(reduction.bridge.affine.variables), True, 0.0, None):
            with self.subTest(target_mask=mask), self.assertRaises(ValueError):
                reduction.project_witness(mask)


if __name__ == "__main__":
    unittest.main()
