"""Semantic checks against independent finite enumeration, with fixed seeds."""

from itertools import product
import random
import unittest

from pnp_lab.affine import AffineRelation


def raw_holds(scope, rows, named):
    # Do not use the production mask intersection/popcount implementation.
    return all(sum(named[name] for index, name in enumerate(scope) if (mask >> index) & 1) % 2 == rhs
               for mask, rhs in rows)


class AffineTests(unittest.TestCase):
    def test_random_projection_against_independent_existential_enumeration(self):
        rng = random.Random(20261104)
        for trial in range(120):
            n = rng.randrange(7)
            scope = tuple(f"v{index}" for index in range(n))
            witness = rng.randrange(1 << n)
            rows = []
            for _ in range(rng.randrange(n + 4)):
                mask = rng.randrange(1 << n)
                rhs = ((mask & witness).bit_count() % 2) if trial % 2 == 0 else rng.randrange(2)
                rows.append((mask, rhs))
            relation = AffineRelation(scope, tuple(rows))
            keep = list(rng.sample(scope, rng.randrange(n + 1)))
            rng.shuffle(keep)
            hidden = tuple(name for name in scope if name not in keep)
            projected = relation.project(keep)
            for boundary in product((0, 1), repeat=len(keep)):
                named_boundary = dict(zip(keep, boundary))
                expected = any(raw_holds(scope, rows, named_boundary | dict(zip(hidden, auxiliary)))
                               for auxiliary in product((0, 1), repeat=len(hidden)))
                self.assertEqual(projected.holds(named_boundary), expected,
                                 (trial, scope, rows, keep, boundary))

    def test_random_join_against_independent_conjunction(self):
        rng = random.Random(714030)
        universe = tuple("abcdef")
        for trial in range(80):
            scopes = [tuple(rng.sample(universe, rng.randrange(7))) for _ in range(2)]
            rows = [tuple((rng.randrange(1 << len(scope)), rng.randrange(2))
                          for _ in range(rng.randrange(7))) for scope in scopes]
            left, right = (AffineRelation(scope, equations) for scope, equations in zip(scopes, rows))
            joined = left.join(right)
            self.assertEqual(joined, left.conjoin(right))
            self.assertEqual(joined.variables, scopes[0] + tuple(name for name in scopes[1] if name not in scopes[0]))
            for values in product((0, 1), repeat=len(joined.variables)):
                named = dict(zip(joined.variables, values))
                expected = raw_holds(scopes[0], rows[0], named) and raw_holds(scopes[1], rows[1], named)
                self.assertEqual(joined.holds(named), expected, (trial, named))

    def test_shared_hidden_variable_must_be_joined_before_projection(self):
        left = AffineRelation.from_named(("x", "h"), [(("x", "h"), 0)])
        right = AffineRelation.from_named(("h", "y"), [(("h", "y"), 1)])
        together = left.join(right).project(("x", "y"))
        self.assertEqual(together.equations, ((3, 1),))
        self.assertEqual(left.project(("x",)).join(right.project(("y",))).equations, ())

    def test_contradictions_empty_scopes_and_reordered_columns(self):
        self.assertTrue(AffineRelation.truth().holds_mask(0))
        self.assertFalse(AffineRelation.false().holds_mask(0))
        contradictory = AffineRelation(("x",), ((1, 0), (1, 1)))
        self.assertFalse(contradictory.project(()).is_consistent)
        self.assertEqual(contradictory.project(()).equations, ((0, 1),))
        system = AffineRelation.from_named(("a", "b", "c"), [(("a", "c"), 1), (("b",), 0)])
        reordered = system.reorder(("c", "a", "b"))
        for values in product((0, 1), repeat=3):
            named = dict(zip(system.variables, values))
            self.assertEqual(system.holds(named), reordered.holds(named))
        self.assertEqual(reordered.reorder(system.variables), system)
        self.assertTrue(system.project(()).holds_mask(0))
        self.assertEqual(system.exists(("b", "c")), system.project(("a",)))

    def test_named_cancellation_canonicalization_and_invalid_inputs(self):
        self.assertEqual(AffineRelation.from_named(("a",), [(("a", "a"), 0)]), AffineRelation.truth(("a",)))
        self.assertEqual(AffineRelation.from_named(("a",), [(("a", "a"), 1)]), AffineRelation.false(("a",)))
        self.assertEqual(AffineRelation(("a", "b"), ((3, 1), (1, 0))),
                         AffineRelation(("a", "b"), ((2, 1), (3, 1), (2, 1))))
        for variables, rows in [(("x", "x"), ()), (("x",), ((2, 0),)), (("x",), ((-1, 0),)), ((), ((0, 2),))]:
            with self.assertRaises(ValueError):
                AffineRelation(variables, rows)
        with self.assertRaises(ValueError):
            AffineRelation.truth(("x",)).project(("missing",))
        with self.assertRaises(ValueError):
            AffineRelation.truth(("x",)).project(("x", "x"))
        with self.assertRaises(ValueError):
            AffineRelation.truth(("x",)).reorder(())


if __name__ == "__main__":
    unittest.main()
