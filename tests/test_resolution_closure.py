import copy
from itertools import combinations
import unittest

from pnp_lab.modular_barrier import line_fixture
from pnp_lab.resolution_closure import (
    ResolutionReplayLimit, check_resolution, check_width_closure,
    replay_resolution, resolution_refute)
from pnp_lab.ternary_flow import scramble


def satisfies(cs, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs)


def naive_width_closure(cs, width):
    """Small independent reference: no masks, agendas, or subsumption deletion."""
    rows = {frozenset(c) for c in cs if len(set(c)) <= width and
            not any(-l in c for l in c)}
    while True:
        if frozenset() in rows:
            return True
        new = set()
        for a, b in combinations(tuple(rows), 2):
            for v in a:
                if -v not in b:
                    continue
                c = (a - {v}) | (b - {-v})
                if len(c) <= width and not any(-l in c for l in c):
                    new.add(c)
        if new <= rows:
            return False
        rows.update(new)


class ResolutionClosureTests(unittest.TestCase):
    def test_exact_width_on_the_integer_blind_fixture(self):
        n, cs = line_fixture(0)
        cs = cs[:152]
        small = resolution_refute(n, cs, width=3)
        self.assertEqual(small['status'], 'UNKNOWN')
        self.assertTrue(small['stats']['complete'])
        self.assertFalse(small['stats']['budget_limited'])
        self.assertEqual(small['stats']['stored_rows'], 152)
        self.assertTrue(check_width_closure(n, cs, small['closure_certificate']))
        larger = resolution_refute(n, cs, width=4)
        self.assertEqual(larger['status'], 'UNSAT')
        self.assertTrue(check_resolution(n, cs, larger['certificate']))
        self.assertEqual(larger['stats']['certificate_width'], 4)
        self.assertEqual(larger['stats']['certificate_parent_union_width'], 5)
        self.assertGreater(larger['stats']['stored_rows'],
                           larger['stats']['certificate_nodes'])
        self.assertFalse(check_resolution(n, tuple(tuple(map(abs, c)) for c in cs),
                                          larger['certificate']))

    def test_all_two_bit_formulas_against_truth_and_independent_width_saturation(self):
        clauses = [(), (1,), (-1,), (2,), (-2,),
                   (1, 2), (1, -2), (-1, 2), (-1, -2)]
        for mask in range(1 << len(clauses)):
            cs = [c for j, c in enumerate(clauses) if mask >> j & 1]
            sat = any(satisfies(cs, word) for word in range(4))
            for width in (0, 1, 2):
                out = resolution_refute(2, cs, width=width,
                                         max_rows=None, max_pairs=None, max_subsets=None)
                refuted = out['status'] == 'UNSAT'
                self.assertEqual(refuted, naive_width_closure(cs, width), (mask, width))
                if refuted:
                    self.assertFalse(sat)
                    self.assertTrue(check_resolution(2, cs, out['certificate']))
                else:
                    self.assertTrue(out['stats']['complete'])
                    self.assertTrue(check_width_closure(2, cs, out['closure_certificate']))
                if width == 2:
                    self.assertEqual(refuted, not sat)

    def test_signed_permutation_and_certificate_tampering(self):
        n, cs = line_fixture(0)
        cs, _ = scramble(n, cs[:152], None, 16002)
        out = resolution_refute(n, cs)
        self.assertEqual(out['status'], 'UNSAT')
        cert = out['certificate']
        rows = replay_resolution(n, cs, cert)
        self.assertFalse(rows[-1])
        first = next(i for i, node in enumerate(cert['nodes']) if node['op'] == 'resolve')
        for change in ('input', 'future', 'pivot', 'root', 'width', 'boolean_index'):
            bad = copy.deepcopy(cert)
            if change == 'input':
                bad['nodes'][0]['clause'] = len(cs)
            elif change == 'future':
                bad['nodes'][first]['left'] = first
            elif change == 'pivot':
                bad['nodes'][first]['pivot'] *= -1
            elif change == 'root':
                bad['root'] -= 1
            elif change == 'width':
                bad['width'] = 3
            else:
                bad['nodes'][0]['clause'] = True
            self.assertFalse(check_resolution(n, cs, bad), change)

    def test_resource_caps_do_not_claim_a_proof_or_a_complete_closure(self):
        n, cs = line_fixture(0)
        cs = cs[:152]
        for kwargs in (dict(max_rows=0), dict(max_pairs=0), dict(max_subsets=0),
                       dict(max_rows=200), dict(max_pairs=10)):
            out = resolution_refute(n, cs, **kwargs)
            self.assertEqual(out['status'], 'UNKNOWN')
            self.assertTrue(out['stats']['budget_limited'])
            self.assertFalse(out['stats']['complete'])
            self.assertIsNone(out['certificate'])
            self.assertIsNone(out['closure_certificate'])
        for name in ('width', 'max_rows', 'max_pairs', 'max_subsets'):
            for value in (-1, True, 0.5):
                with self.assertRaises(ValueError):
                    resolution_refute(0, [], **{name: value})

    def test_closure_checker_requires_axioms_and_every_usable_resolvent(self):
        cs = [(1,), (-1, 2)]
        good = dict(kind='bounded-resolution-closure-v1', width=2,
                    clauses=[[1], [2]])
        self.assertTrue(check_width_closure(2, cs, good))
        missing_axiom = copy.deepcopy(good)
        missing_axiom['clauses'] = [[1]]
        self.assertFalse(check_width_closure(2, cs, missing_axiom))
        missing_resolvent = copy.deepcopy(good)
        missing_resolvent['clauses'] = [[1], [-1, 2]]
        self.assertFalse(check_width_closure(2, cs, missing_resolvent))
        for clause in ([], [1, -1], [1, 1], [3]):
            bad = copy.deepcopy(good)
            bad['clauses'].append(clause)
            self.assertFalse(check_width_closure(2, cs, bad))
        self.assertFalse(check_width_closure(2, [()], good))

    def test_empty_inputs_normalization_and_sparse_variable_names(self):
        empty = resolution_refute(0, [], width=0)
        self.assertEqual(empty['status'], 'UNKNOWN')
        self.assertTrue(check_width_closure(0, [], empty['closure_certificate']))
        false = resolution_refute(0, [()], width=0)
        self.assertEqual(false['status'], 'UNSAT')
        self.assertTrue(check_resolution(0, [()], false['certificate']))
        cs = [(1, -1), (1, 1), (-1, -1)]
        q = resolution_refute(1, cs, width=1)
        self.assertEqual(q['status'], 'UNSAT')
        self.assertTrue(check_resolution(1, cs, q['certificate']))
        self.assertEqual([t['clause'] for t in q['certificate']['nodes']
                          if t['op'] == 'input'], [1, 2])
        huge = 10**12
        q = resolution_refute(huge, [(huge,), (-huge,)], width=1)
        self.assertEqual(q['status'], 'UNSAT')
        self.assertEqual(q['stats']['mask_coordinate_bits'], 2)
        self.assertTrue(check_resolution(huge, [(huge,), (-huge,)], q['certificate']))

    def test_replay_caps_use_actual_width_and_are_distinct_from_malformed_proofs(self):
        cs = [(1,), (-1,)]
        cert = resolution_refute(1, cs, width=1)['certificate']
        cert['width'] = 1000  # A loose declaration must not allocate a large table.
        self.assertTrue(check_resolution(1, cs, cert, max_nodes=3, max_width=1,
                                         max_literal_occurrences=2))
        for cap in (dict(max_nodes=2), dict(max_width=0), dict(max_literal_occurrences=1)):
            with self.assertRaises(ResolutionReplayLimit):
                replay_resolution(1, cs, cert, **cap)
            self.assertFalse(check_resolution(1, cs, cert, **cap))
        bad = copy.deepcopy(cert)
        bad['nodes'][-1]['left'] = 2
        try:
            replay_resolution(1, cs, bad, max_nodes=3)
        except ValueError as exc:
            self.assertNotIsInstance(exc, ResolutionReplayLimit)
        else:
            self.fail('a forward parent reference passed replay')
        empty = resolution_refute(0, [()], width=0)['certificate']
        self.assertTrue(check_resolution(0, [()], empty, max_nodes=1, max_width=0,
                                         max_literal_occurrences=0))

