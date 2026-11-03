"""Check a three-option support reduction against raw source and target semantics."""

from functools import reduce
from collections import Counter
from itertools import product
from operator import xor
import random
import unittest

from pnp_lab.ternary_support import (decide_ternary_reduction, three_cnf_to_ternary_supports,
                                     three_cnf_to_weight_two_supports)


def source_models(n, clauses):
    out = []
    for bits in product((False, True), repeat=n):
        if all(any(bits[abs(lit)-1] == (lit > 0) for lit in clause) for clause in clauses):
            out.append(sum(int(bit) << i for i, bit in enumerate(bits)))
    return out


class TernarySupportTests(unittest.TestCase):
    def raw_roundtrips(self, variables, clauses):
        red = three_cnf_to_ternary_supports(variables, clauses)
        active = sum(1 << i for i, broadcast in enumerate(red.variable_masks) if broadcast)
        models = source_models(len(variables), clauses)
        for compiled in (red, three_cnf_to_weight_two_supports(variables, clauses)):
            for mask in range(1 << len(variables)):
                if mask not in models:
                    with self.assertRaises(ValueError):
                        compiled.lift_witness(mask)
                    continue
                values = compiled.lift_witness(mask)
                self.assertEqual(len(values), len(compiled.supports))
                self.assertTrue(all(v in s for v, s in zip(values, compiled.supports)))
                self.assertEqual(reduce(xor, values, 0), 0)
                self.assertEqual(compiled.project_witness(values), mask & active)
            result = decide_ternary_reduction(compiled)
            self.assertEqual(result["status"], "SAT" if models else "UNSAT")
            if models:
                self.assertIn(result["source_witness_mask"], models)
                self.assertEqual(result["source_witness_mask"], compiled.project_witness(result["witness"]))
            else:
                self.assertIsNone(result["source_witness_mask"])
        return red

    def test_one_positive_clause_full_cartesian_target_oracle_not_parsimonious(self):
        red = self.raw_roundtrips(("x", "y", "z"), ((1, 2, 3),))
        choices = [x for x in product(*red.supports) if reduce(xor, x, 0) == 0]
        self.assertEqual(len(choices), 12)
        self.assertEqual({red.project_witness(x) for x in choices}, set(range(1, 8)))
        for x in choices:  # raw broadcasts decode to the same assignment
            self.assertEqual(red.project_witness(x), sum((v != 0) << i for i, v in enumerate(x[:3])))

    def test_shared_variables_signed_repeated_and_short_clauses(self):
        for clauses in (((-1,), (-1, 2)), ((1, -1, 1), (-2,)), ((1,), (-1,)),
                        ((-1, -1), (2, 1)), ((2, 2, 2),), ((-1, -2, -1),)):
            with self.subTest(clauses=clauses):
                red = self.raw_roundtrips(("x", "y", "unused"), clauses)
                # Exhaust true target choices by raw XOR, separately from frontier search.
                decoded = {red.project_witness(x) for x in product(*red.supports)
                           if reduce(xor, x, 0) == 0}
                active = sum(1 << i for i, b in enumerate(red.variable_masks) if b)
                self.assertEqual(decoded, {a & active for a in source_models(3, clauses)})

    def test_explicit_scope_empty_clause_and_empty_conjunction(self):
        for variables, clauses in (((), ()), (("free", "more"), ()),
                                   ((), ((),)), (("x",), ((1,), (), (-1,)))):
            with self.subTest(variables=variables, clauses=clauses):
                red = self.raw_roundtrips(variables, clauses)
                if () in clauses:
                    self.assertIn((), red.supports)
                    self.assertEqual(decide_ternary_reduction(red, max_transitions=0)["status"], "UNSAT")
                else:
                    self.assertEqual(red.supports, ((0,),) * len(variables))
                    self.assertEqual(red.project_witness([0] * len(variables)), 0)

    def test_construction_bounds_and_exact_incidence(self):
        variables = ("x", "y", "z", "unused")
        clauses = [(1, -3, 1), (3, -2), (2,), (1, -1, 3)]
        red = three_cnf_to_ternary_supports(iter(variables), (iter(c) for c in clauses))
        n, m, t = len(variables), len(clauses), sum(map(len, clauses))
        self.assertEqual(red.original_variables, variables)
        self.assertEqual(red.original_cnf, tuple(clauses))
        self.assertEqual([j for ids in red.clause_occurrences for j in ids], list(range(t)))
        self.assertEqual(len(red.supports), n+m+t)
        touched = [set() for _ in range(2*t)]
        for g, group in enumerate(red.supports):
            self.assertLessEqual(len(group), 3)
            self.assertEqual(len(group), len(set(group)))
            for mask in group:
                self.assertLess(mask, 1 << (2*t))
                for bit in range(2*t):
                    if mask >> bit & 1:
                        touched[bit].add(g)
        for c, (clause, ids) in enumerate(zip(clauses, red.clause_occurrences)):
            for lit, j in zip(clause, ids):
                self.assertEqual(touched[2*j], {abs(lit)-1, n+m+j})
                self.assertEqual(touched[2*j+1], {n+c, n+m+j})

    def test_fixed_seed_solver_compared_with_raw_source_assignment_oracle(self):
        rng = random.Random(602352)
        for i in range(70):
            n = rng.randint(1, 4)
            clauses = tuple(tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                                  for _ in range(rng.randint(1, 3)))
                            for _ in range(rng.randint(1, 3)))
            with self.subTest(i=i):
                self.raw_roundtrips(tuple(f"x{j}" for j in range(n)), clauses)

    def test_nonlinear_images_are_solved_and_budget_is_not_a_negative_answer(self):
        for names, clauses, answer in (
            (("x", "y", "z"), ((1, 2, 3), (-1, -2, -3)), "SAT"),
            (("x",), ((1, 1, 1), (-1, -1, -1)), "UNSAT"),
        ):
            red = three_cnf_to_ternary_supports(names, clauses)
            result = decide_ternary_reduction(red)
            self.assertEqual(result["status"], answer)
            self.assertGreater(result["residual_groups"], 0)
            self.assertGreater(result["transitions"], 0)
            partial = decide_ternary_reduction(red, max_transitions=0)
            self.assertEqual(partial["status"], "UNKNOWN")
            self.assertIsNone(partial["source_witness_mask"])

    def test_weight_two_port_owners_and_true_masks_on_copy_cycles(self):
        # x appears six times, y twice (parallel equality ports), z once, u never.
        red = three_cnf_to_weight_two_supports(("x", "y", "z", "u"),
                                              ((1, 2, 3), (1, -2, 1), (1, 1, -1)))
        self.assertEqual((len(red.supports), red.n_coordinates), (21, 26))
        owners = [set() for _ in range(red.n_coordinates)]
        for i, s in enumerate(red.supports):
            self.assertLessEqual(len(s), 3)
            for mask in s:
                self.assertLessEqual(mask.bit_count(), 2)
                while mask:
                    one = mask & -mask
                    owners[one.bit_length()-1].add(i)
                    mask ^= one
        self.assertTrue(all(len(s) == 2 for s in owners))
        yy = [mask for owner, mask in zip(red.occurrence_variables, red.copy_one_masks) if owner == 1]
        self.assertEqual(len(yy), 2)
        self.assertEqual(yy[0], yy[1])
        self.assertEqual(yy[0].bit_count(), 2)
        self.assertEqual(red.copy_one_masks[2], 0)
        self.assertGreater(max(x.bit_count() for s in red.direct.supports for x in s), 2)

    def test_weight_two_exhaustive_target_fibers_equal_direct_target_fibers(self):
        for cnf in (((1, 1, -2),), ((-1, -1), (2,)), ((1,), (-1,)), ((1, 2, -1),), ()):
            red = three_cnf_to_weight_two_supports(("x", "y", "unused"), cnf)
            fibers = [Counter(compiled.project_witness(choices)
                              for choices in product(*compiled.supports) if reduce(xor, choices, 0) == 0)
                      for compiled in (red, red.direct)]
            self.assertEqual(*fibers)
            active = sum(1 << i for i, x in enumerate(red.direct.variable_masks) if x)
            self.assertEqual(set(fibers[0]), {x & active for x in source_models(3, cnf)})

    def test_weight_two_invalid_choice_and_budget(self):
        red = three_cnf_to_weight_two_supports(("x", "y", "z"), ((1, 2, 3), (-1, -2, -3)))
        choices = red.lift_witness(1)
        bad = (next(x for x in red.supports[0] if x != choices[0]),) + choices[1:]
        with self.assertRaises(ValueError):
            red.project_witness(bad)
        with self.assertRaises(ValueError):
            red.project_witness(choices[:-1])
        undecided = decide_ternary_reduction(red, max_transitions=0)
        self.assertEqual(undecided["status"], "UNKNOWN")
        self.assertIsNone(undecided["source_witness_mask"])

    def test_invalid_inputs_and_nonmodels_are_rejected(self):
        for names, clauses in ((("x", "x"), []), (("",), []), ("x", []),
                               (["x"], "bad"), ([None], []), (["x"], [None]),
                               (["x"], [""]), (["x"], [(), (1, 1, 1, 1)]),
                               (["x"], [(), (0,)]), (["x"], [(2,)]),
                               (["x"], [(True,)]), (["x"], [(-1.0,)])):
            with self.assertRaises(ValueError):
                three_cnf_to_ternary_supports(names, clauses)
        red = three_cnf_to_ternary_supports(("x",), ((1,),))
        for bad in (-1, 2, False, 0, None):
            with self.assertRaises(ValueError):
                red.lift_witness(bad)
        witness = red.lift_witness(1)
        for bad in ((), None, "abc", (-1, *witness[1:]), (True, *witness[1:]),
                    (0, *witness[1:]), (*witness, 0)):
            with self.assertRaises(ValueError):
                red.project_witness(bad)
