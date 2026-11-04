from copy import deepcopy
from itertools import combinations, permutations
from math import gcd
from random import Random
import unittest

from pnp_lab.integer_hull import (
    _integer_eliminate, check_integer_hull, check_integer_row,
    collect_integer_rows, integer_hull_refute)
from pnp_lab.four_flow import four_prism_flow
from pnp_lab.ternary_flow import prism_flow, scramble


def determinant(matrix):
    n = len(matrix)
    return sum((-1 if sum(a > b for i, a in enumerate(p) for b in p[i + 1:]) % 2 else 1)
               * _product(matrix[i][j] for i, j in enumerate(p))
               for p in permutations(range(n)))


def _product(values):
    out = 1
    for x in values:
        out *= x
    return out


def lattice_index(matrix, columns):
    """Rank and saturation index from all minors, independent of elimination."""
    rank, index = 0, 1
    for size in range(1, min(len(matrix), columns) + 1):
        g = 0
        for rows in combinations(range(len(matrix)), size):
            for cols in combinations(range(columns), size):
                g = gcd(g, determinant([[matrix[i][j] for j in cols] for i in rows]))
        if not g:
            break
        rank, index = size, g
    return rank, index


def cycle(n):
    return [(i, i % n + 1) for i in range(1, n + 1)] + [
        (-i, -(i % n + 1)) for i in range(1, n + 1)]


class IntegerHullTests(unittest.TestCase):
    def test_integer_elimination_against_independent_lattice_indices(self):
        rng = Random(150021)
        matrices = [([[2]], [1]), ([[6]], [3]), ([[2, 0], [1, 2]], [0, 1]),
                    ([[1, 1, 0], [0, 1, 1], [1, 0, 1]], [1, 1, 1]),
                    ([[]], [1]), ([], [])]
        for _ in range(350):
            m, n = rng.randrange(4), rng.randrange(4)
            matrices.append(([[rng.randrange(-3, 4) for _ in range(n)] for _ in range(m)],
                             [rng.randrange(-4, 5) for _ in range(m)]))
        for a, b in matrices:
            n = len(a[0]) if a else 0
            expected = lattice_index(a, n) == lattice_index([r + [x] for r, x in zip(a, b)], n + 1)
            equations = [({j: x for j, x in enumerate(r) if x}, h) for r, h in zip(a, b)]
            result = _integer_eliminate(equations)
            self.assertNotEqual(result['status'], 'UNKNOWN', (a, b, result))
            self.assertEqual(result['status'] == 'FEASIBLE', expected, (a, b, result))
            if not expected:
                m, proof = result['modulus'], result['proof']
                total = [sum(c * a[i][j] for i, c in proof.items()) for j in range(n)]
                rhs = sum(c * b[i] for i, c in proof.items())
                self.assertFalse(any(x % m if m else x for x in total))
                self.assertTrue(rhs % m if m else rhs)

    def test_all_three_bit_relations_produce_sound_raw_laws(self):
        for table in range(256):
            clauses = [tuple(v * (-1 if w >> (v - 1) & 1 else 1) for v in (1, 2, 3))
                       for w in range(8) if not (table >> w & 1)]
            laws, stats = collect_integer_rows(3, clauses, scopes=[(1, 2, 3)])
            self.assertTrue(stats['scope_complete'])
            self.assertTrue(all(check_integer_row(3, clauses, row) for row in laws))
            answer = integer_hull_refute(3, clauses, scopes=[(1, 2, 3)])
            self.assertEqual(answer['status'], 'UNKNOWN' if table else 'UNSAT')
            if table:
                self.assertTrue(answer['stats']['integer_feasible'])
                self.assertIsNone(answer['witness'])
            else:
                self.assertTrue(check_integer_hull(3, clauses, answer['certificate']))

    def test_global_modulus_appears_after_torsion_free_local_tables(self):
        clauses, _ = scramble(11, cycle(11), None, 150211)
        answer = integer_hull_refute(11, clauses)
        self.assertEqual(answer['status'], 'UNSAT')
        self.assertEqual(answer['stats']['discovered_modulus'], 2)
        self.assertEqual(answer['stats']['congruence_rows'], 0)
        self.assertEqual(list(answer['stats']['local_torsion_histogram']), ['[]'])
        self.assertTrue(answer['stats']['scope_complete'])
        self.assertTrue(check_integer_hull(11, clauses, answer['certificate']))
        even = integer_hull_refute(12, cycle(12))
        self.assertEqual(even['status'], 'UNKNOWN')
        self.assertTrue(even['stats']['integer_feasible'])

    def test_prior_hidden_fields_and_composite_arithmetic_without_hint(self):
        for generator, expected in ((prism_flow, 3), (four_prism_flow, 4)):
            for bad in (False, True):
                n, clauses, word = generator(4, bad)
                clauses, _ = scramble(n, clauses, word, 150304 + expected)
                answer = integer_hull_refute(n, clauses)
                self.assertEqual(answer['status'], 'UNSAT' if bad else 'UNKNOWN')
                self.assertTrue(answer['stats']['scope_complete'])
                if bad:
                    self.assertEqual(answer['stats']['discovered_modulus'], expected)
                    self.assertTrue(check_integer_hull(n, clauses, answer['certificate']))
                    if expected == 4:
                        self.assertEqual(answer['certificate']['residual_rhs'], 2)
                else:
                    self.assertTrue(answer['stats']['integer_feasible'])
                    self.assertIsNone(answer['witness'])

    def test_certificate_tampering_and_original_clause_binding(self):
        n, clauses, _ = four_prism_flow(4, True)
        cert = integer_hull_refute(n, clauses)['certificate']
        self.assertTrue(check_integer_hull(n, clauses, cert))
        for field, value in (('modulus', 0), ('modulus', 1), ('modulus', 2),
                             ('modulus', True), ('residual_rhs', 1), ('residual_rhs', True)):
            bad = deepcopy(cert)
            bad[field] = value
            self.assertFalse(check_integer_hull(n, clauses, bad))
        for field, value in (('weight', False), ('weight', 0), ('rhs', 927),
                             ('clauses', [len(clauses)]), ('clauses', [False]),
                             ('scope', [1, 1]), ('modulus', 3)):
            bad = deepcopy(cert)
            bad['terms'][0][field] = value
            self.assertFalse(check_integer_hull(n, clauses, bad), (field, value))
        odd = cycle(11)
        proof = integer_hull_refute(11, odd)['certificate']
        # Change one disequality edge into equality: the same cycle is now SAT.
        good = odd.copy()
        good[0], good[11] = (-1, 2), (1, -2)
        self.assertFalse(check_integer_hull(11, good, proof))
        self.assertFalse(check_integer_hull(11, odd, dict(proof, terms=[])))

    def test_caps_never_claim_absence_of_an_obstruction(self):
        for cap in (dict(max_scopes=0), dict(max_rows=0), dict(max_columns=0),
                    dict(max_ops=0), dict(max_bits=0), dict(max_models=1),
                    dict(max_local_ops=0)):
            result = integer_hull_refute(11, cycle(11), **cap)
            self.assertEqual(result['status'], 'UNKNOWN', cap)
            self.assertTrue(result['stats']['budget_limited'], cap)
            self.assertIsNone(result['certificate'])
        for bad in (dict(max_ops=-1), dict(max_bits=True), dict(max_columns=-1),
                    dict(max_rows=-1), dict(scopes=[(1, 1)]), dict(scopes=[(12,)])):
            with self.assertRaises(ValueError):
                integer_hull_refute(11, cycle(11), **bad)
        empty = integer_hull_refute(0, [])
        self.assertEqual(empty['status'], 'UNKNOWN')
        self.assertTrue(empty['stats']['integer_feasible'])
        refuted = integer_hull_refute(0, [()])
        self.assertEqual(refuted['status'], 'UNSAT')
        self.assertEqual(refuted['certificate']['modulus'], 0)
        self.assertTrue(check_integer_hull(0, [()], refuted['certificate']))
