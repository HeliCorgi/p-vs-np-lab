from collections import Counter
from itertools import combinations
import unittest

from pnp_lab.feedback_fixture import cubic_tseitin, feedback_case, shield_clauses
from pnp_lab.modular_padding import peel
from pnp_lab.ternary_flow import scramble


def holds(cs, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs)


class FeedbackFixtureTests(unittest.TestCase):
    def test_exact_projection_and_deterministic_lifting(self):
        base = [(1, -2, -3)]
        for all_sockets in (False, True):
            n, rows, _ = shield_clauses(3, base, layers=1, all_sockets=all_sockets)
            actual = {x & 7 for x in range(1 << n) if holds(rows, x)}
            self.assertEqual(actual, {x for x in range(8) if holds(base, x)})
            for x in actual:
                _, _, y = shield_clauses(3, base, layers=1, word=x, all_sockets=all_sockets)
                self.assertEqual(y & 7, x)
                self.assertTrue(holds(rows, y))

    def test_exact_retraction_of_every_raw_clause(self):
        base = [(1, -2, -3), (-1, 2, 3), (2, 1, -3)]
        L = 2
        for all_sockets in (False, True):
            n, rows, _ = shield_clauses(3, base, layers=L, all_sockets=all_sockets)
            images = [0, 1, 2, 3]
            for c in base:
                for target in (c if all_sockets else c[-1:]):
                    images.extend([target] * (1 + 2 * L))
            self.assertEqual(len(images), n + 1)
            out = []
            for raw in rows:
                mapped = set((1 if l > 0 else -1) * images[abs(l)] for l in raw)
                if not any(-l in mapped for l in mapped):
                    out.append(frozenset(mapped))
            self.assertEqual(out, list(map(frozenset, base)))

    def test_scoped_unit_flips_include_internal_and_original_coordinates(self):
        # For all scopes of size <=3 in one small gadget with four layers,
        # inspect *only clauses contained in the scope*. Pairs differing by a
        # single bit in every direction certify a full integer affine lattice.
        for all_sockets in (False, True):
            n, rows, _ = shield_clauses(3, [(-1, 2, -3)], layers=4, all_sockets=all_sockets)
            supports = [(set(map(abs, row)), row) for row in rows]
            for k in range(1, 4):
                for scope in combinations(range(1, n+1), k):
                    ids = {v: j+1 for j, v in enumerate(scope)}
                    fragment = [tuple(ids[abs(l)] * (1 if l > 0 else -1) for l in row)
                                for variables, row in supports if variables <= ids.keys()]
                    models = {x for x in range(1 << k) if holds(fragment, x)}
                    for j in range(k):
                        self.assertTrue(any(x ^ (1 << j) in models for x in models))

    def test_anchors_and_signed_eligibility(self):
        for fully in (False, True):
            n, rows, word, core = feedback_case(6, False, layers=3, all_sockets=fully)
            self.assertTrue(holds(rows, word))
            freq = Counter(abs(l) for c in rows if len(c) == 3 for l in c)
            self.assertEqual({v for v, count in freq.items() if count >= 2},
                             set() if fully else {abs(l) for c in core for l in c})
            raw, y = scramble(n, rows, word, 143)
            self.assertTrue(holds(raw, y))
            self.assertEqual(peel(n, raw)[1], [])

    def test_invalid_width_graph_and_word(self):
        for c in [(1, 2), (1, -1, 2), (1, 1, 3), (True, 2, 3), (1, 2, 4)]:
            with self.assertRaises(ValueError):
                shield_clauses(3, [c])
        for kwargs in (dict(layers=0), dict(layers=True), dict(word=0),
                       dict(word=8), dict(all_sockets=1)):
            with self.assertRaises(ValueError):
                shield_clauses(3, [(1, 2, 3)], **kwargs)
        for edges, q in (([(0, 0)], [0]), ([(0, 1), (1, 0)], [0, 0]),
                         ([(0, 1)], [0, 0]), ([(0, 1)], [0, 2])):
            with self.assertRaises(ValueError):
                cubic_tseitin(edges, q)
