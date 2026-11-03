"""Semantic tests for finite relations; direct enumeration is the reference."""

from itertools import product
from math import factorial
import unittest

from pnp_lab.relations import (
    ColorLiteral,
    FiniteRelation,
    canonical_partitions,
    canonicalize_colors,
    clause_holds,
    cnf_holds,
    conjoin_all,
)


class CanonicalPartitionsTests(unittest.TestCase):
    def test_color_renaming_preserves_position_order(self):
        self.assertEqual(canonicalize_colors((7, 4, 7, 9)), (0, 1, 0, 2))
        self.assertEqual(canonicalize_colors((4, 7, 7, 9)), (0, 1, 1, 2))
        self.assertEqual(canonicalize_colors(()), ())

    def test_partition_counts_and_palette_cap(self):
        for length, colors, expected in ((0, 3, 1), (3, 3, 5), (4, 4, 15), (4, 2, 8), (5, 5, 52)):
            with self.subTest(length=length, colors=colors):
                states = tuple(canonical_partitions(length, colors))
                self.assertEqual(len(states), expected)
                self.assertEqual(states, tuple(sorted(set(states))))
                self.assertTrue(all(row == canonicalize_colors(row) for row in states))
                self.assertTrue(all(len(set(row)) <= colors for row in states))


class FiniteRelationTests(unittest.TestCase):
    def test_input_validation(self):
        for variables, colors, rows in (
            (("a", "a"), 3, {(0, 1)}),
            (("a",), 0, {(0,)}),
            (("a",), 3, {(3,)}),
            (("a",), 3, {(0, 1)}),
        ):
            with self.subTest(variables=variables, colors=colors, rows=rows):
                with self.assertRaises(ValueError):
                    FiniteRelation(variables, colors, rows)

    def test_join_matches_direct_predicate_with_reordered_shared_scope(self):
        left = FiniteRelation.from_predicate(("a", "s", "t"), 3, lambda c: c["a"] != c["s"] and c["s"] == c["t"])
        right = FiniteRelation.from_predicate(("t", "s", "b"), 3, lambda c: c["t"] != c["b"] and c["s"] == c["t"])
        joined = left.join(right)
        expected = {
            (a, s, t, b) for a, s, t, b in product(range(3), repeat=4)
            if a != s and s == t and t != b
        }
        self.assertEqual(joined.variables, ("a", "s", "t", "b"))
        self.assertEqual(joined.rows, expected)
        self.assertEqual(right.join(left).project(joined.variables), joined)
        self.assertEqual(left.conjoin(right), joined)

    def test_join_keeps_actual_named_color_labels(self):
        left = FiniteRelation(("a", "x"), 3, {(2, 1)})
        right = FiniteRelation(("x", "b"), 3, {(1, 2)})
        self.assertEqual(left.join(right).rows, {(2, 1, 2)})
        incompatible = FiniteRelation(("x", "b"), 3, {(0, 2)})
        self.assertFalse(left.join(incompatible).rows)

    def test_projection_order_and_empty_scope_truth(self):
        relation = FiniteRelation(("a", "x", "b"), 3, {(0, 1, 2), (0, 2, 2)})
        self.assertEqual(relation.project(("b", "a")).rows, {(2, 0)})
        self.assertEqual(relation.exists(("x",)), relation.project(("a", "b")))
        self.assertEqual(relation.project(()).rows, {()})
        empty = FiniteRelation(("a",), 3, set())
        self.assertEqual(empty.project(()).rows, set())
        with self.assertRaises(ValueError):
            relation.project(("unknown",))
        with self.assertRaises(ValueError):
            relation.project(("a", "a"))
        with self.assertRaises(ValueError):
            relation.exists(("unknown",))

    def test_named_color_pinning_does_not_get_a_symmetric_summary(self):
        pinned = FiniteRelation(("a",), 3, {(2,)})
        self.assertFalse(pinned.is_color_symmetric())
        with self.assertRaises(ValueError):
            pinned.canonical_rows()
        joined = pinned.join(FiniteRelation.disequality("a", "b", 3))
        self.assertEqual(joined.project(("b",)).rows, {(0,), (1,)})
        symmetric = FiniteRelation.equality("a", "b", 3)
        self.assertEqual(symmetric.canonical_rows(), ((0, 0),))

    def test_conjunction_identity_contradiction_and_palette_mismatch(self):
        equal = FiniteRelation.equality("a", "b", 3)
        different = FiniteRelation.disequality("a", "b", 3)
        self.assertEqual(FiniteRelation.truth(3).join(equal), equal)
        self.assertEqual(conjoin_all((), 3), FiniteRelation.truth(3))
        self.assertFalse(equal.join(different).rows)
        self.assertEqual(FiniteRelation.equality("a", "a", 3).rows, {(0,), (1,), (2,)})
        self.assertFalse(FiniteRelation.disequality("a", "a", 3).rows)
        with self.assertRaises(ValueError):
            equal.join(FiniteRelation.truth(4))

    def test_shared_boundary_composition_equals_direct_graph_exists(self):
        # The two interiors share only a,b. Their projected relations may be
        # conjoined because internal x and y are independent after fixing a,b.
        first = FiniteRelation.from_predicate(("a", "b", "x"), 3, lambda c: c["a"] != c["x"] and c["b"] != c["x"])
        second = FiniteRelation.from_predicate(("b", "a", "y"), 3, lambda c: c["a"] != c["y"] and c["b"] == c["y"])
        composed = first.join(second).project(("a", "b"))
        projected_then_joined = first.project(("a", "b")).join(second.project(("a", "b")))
        direct = {
            (a, b) for a, b in product(range(3), repeat=2)
            if any(a != x and b != x and a != y and b == y for x, y in product(range(3), repeat=2))
        }
        self.assertEqual(composed.rows, direct)
        self.assertEqual(projected_then_joined, composed)

    def test_star_projection_matches_direct_exists_and_exact_formula(self):
        for q, bell in ((3, 5), (4, 15), (5, 52)):
            with self.subTest(q=q):
                ports = tuple(f"t{i}" for i in range(q))
                star = conjoin_all((FiniteRelation.disequality(port, "x", q) for port in ports), q)
                projected = star.project(ports)
                direct = {
                    boundary for boundary in product(range(q), repeat=q)
                    if any(all(center != color for color in boundary) for center in range(q))
                }
                self.assertEqual(projected.rows, direct)
                self.assertEqual(len(projected.rows), q ** q - factorial(q))
                self.assertEqual(len(projected.canonical_rows()), bell - 1)
                self.assertNotIn(tuple(range(q)), projected.rows)


class ColorClauseTests(unittest.TestCase):
    def test_literals_use_color_predicates_with_transitivity(self):
        assignment = {"a": 2, "b": 2, "c": 2}
        self.assertTrue(ColorLiteral("a", "b").evaluate(assignment))
        self.assertTrue(ColorLiteral("b", "c").evaluate(assignment))
        self.assertTrue(ColorLiteral("a", "c").evaluate(assignment))
        self.assertFalse(ColorLiteral("a", "c", equal=False).evaluate(assignment))
        self.assertFalse(clause_holds((), assignment))
        self.assertTrue(cnf_holds((), assignment))
        self.assertFalse(cnf_holds(((),), assignment))

    def test_cnf_semantics_on_all_labeled_assignments(self):
        clauses = (
            (ColorLiteral("a", "b"), ColorLiteral("b", "c", equal=False)),
            (ColorLiteral("a", "c", equal=False),),
        )
        for a, b, c in product(range(3), repeat=3):
            actual = cnf_holds(clauses, {"a": a, "b": b, "c": c})
            self.assertEqual(actual, (a == b or b != c) and a != c)


if __name__ == "__main__":
    unittest.main()
