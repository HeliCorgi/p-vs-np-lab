import copy
from itertools import product
import unittest

from pnp_lab.parity_query import KIND, check_parity_query, parity_query_refute


def parity_clauses(scope, rhs):
    return [tuple(-v if bit else v for v, bit in zip(scope, word))
            for word in product((0, 1), repeat=len(scope)) if sum(word) % 2 != rhs]


class ParityQueryTests(unittest.TestCase):
    def test_overlapping_blocks_from_raw_and_duplicate_support(self):
        raw = (parity_clauses((1, 2, 3), 0)
               + parity_clauses((2, 3, 4), 1)
               + parity_clauses((1, 4), 0))
        # Extra nonlinear clauses, duplicate literals/clauses, and tautologies
        # do not invalidate a refutation of a correctly recognized subset.
        raw += [(1, 3, 4), (*raw[0], raw[0][0]), raw[0], (1, -1, 4)]
        result = parity_query_refute(4, raw)
        self.assertEqual(result['status'], 'UNSAT')
        self.assertTrue(check_parity_query(4, raw, result['certificate']))
        self.assertLessEqual(result['stats']['leaves'], len(raw))
        all_patterns = parity_clauses((1, 2), 0) + parity_clauses((1, 2), 1)
        result = parity_query_refute(2, all_patterns)
        self.assertEqual(result['stats']['selected_blocks'], 2)
        self.assertEqual(result['stats']['leaves'], 4)
        self.assertTrue(check_parity_query(2, all_patterns, result['certificate']))

    def test_consistent_relaxation_and_missing_pattern_are_unknown(self):
        sat = parity_clauses((1, 2, 3), 0) + parity_clauses((2, 3, 4), 1)
        self.assertEqual(parity_query_refute(4, sat)['status'], 'UNKNOWN')
        self.assertIsNone(parity_query_refute(4, sat)['certificate'])
        raw = parity_clauses((1, 2, 3), 0) + parity_clauses((1, 2, 3), 1)
        for i in range(len(raw)):
            weakened = raw[:i] + raw[i+1:]
            self.assertEqual(parity_query_refute(3, weakened)['status'], 'UNKNOWN')
        self.assertEqual(parity_query_refute(0, [])['status'], 'UNKNOWN')
        self.assertEqual(parity_query_refute(3, [(1, 1, -1), (2, 3)])['status'], 'UNKNOWN')

    def test_generic_path_implication_and_inconsistent_branch(self):
        cert = dict(kind=KIND, root=0, nodes=[
            dict(query=[1], zero=1, one=4),
            dict(query=[1], zero=2, one=3),
            dict(clause=0), dict(inconsistent=True), dict(clause=1)])
        self.assertTrue(check_parity_query(1, [(1,), (-1,)], cert))
        # A parity of two variables alone does not force either coordinate.
        fake = dict(kind=KIND, root=0, nodes=[
            dict(query=[1, 2], zero=1, one=2), dict(clause=0), dict(clause=1)])
        self.assertFalse(check_parity_query(2, [(1,), (-1,)], fake))
        # A single impossible leaf without contradictory path equations is not
        # a refutation, even if the raw formula happens to be unsatisfiable.
        fake = dict(kind=KIND, root=0, nodes=[dict(inconsistent=True)])
        self.assertFalse(check_parity_query(1, [(1,), (-1,)], fake))

    def test_rejects_malformed_and_rebound_certificates(self):
        raw = [(1,), (-1,)]
        cert = parity_query_refute(1, raw)['certificate']
        self.assertTrue(check_parity_query(1, raw, cert))
        changes = ('kind', 'root_bool', 'extra', 'query_bool', 'query_zero',
                   'query_range', 'query_duplicate', 'missing_branch', 'dag',
                   'cycle', 'orphan', 'clause_bool', 'clause_range', 'wrong_clause',
                   'branch_swap', 'node_extra', 'empty_nodes', 'fake_inconsistent')
        for change in changes:
            bad = copy.deepcopy(cert)
            if change == 'kind': bad['kind'] = 'untrusted'
            elif change == 'root_bool': bad['root'] = False
            elif change == 'extra': bad['axiom'] = 'UNSAT'
            elif change == 'query_bool': bad['nodes'][0]['query'] = [True]
            elif change == 'query_zero': bad['nodes'][0]['query'] = [0]
            elif change == 'query_range': bad['nodes'][0]['query'] = [2]
            elif change == 'query_duplicate': bad['nodes'][0]['query'] = [1, 1]
            elif change == 'missing_branch': del bad['nodes'][0]['one']
            elif change == 'dag': bad['nodes'][0]['one'] = bad['nodes'][0]['zero']
            elif change == 'cycle': bad['nodes'][0]['zero'] = 0
            elif change == 'orphan': bad['nodes'].append(dict(clause=0))
            elif change == 'clause_bool': bad['nodes'][1]['clause'] = False
            elif change == 'clause_range': bad['nodes'][1]['clause'] = 2
            elif change == 'wrong_clause': bad['nodes'][1]['clause'] ^= 1
            elif change == 'branch_swap':
                bad['nodes'][0]['zero'], bad['nodes'][0]['one'] = bad['nodes'][0]['one'], bad['nodes'][0]['zero']
            elif change == 'node_extra': bad['nodes'][1]['proof'] = 'assumed'
            elif change == 'empty_nodes': bad['nodes'].clear()
            else: bad['nodes'][1] = dict(inconsistent=True)
            self.assertFalse(check_parity_query(1, raw, bad), change)
        self.assertFalse(check_parity_query(1, [(1,), (1,)], cert))

    def test_empty_clause_sparse_labels_and_invalid_input(self):
        result = parity_query_refute(0, [()])
        self.assertTrue(check_parity_query(0, [()], result['certificate']))
        self.assertEqual(result['stats']['leaves'], 1)
        n = 10**10
        result = parity_query_refute(n, [(n,), (-n,)])
        self.assertEqual(result['stats']['used_variables'], 1)
        self.assertTrue(check_parity_query(n, [(n,), (-n,)], result['certificate']))
        for n, raw in [(True, []), (-1, []), (1, [(True,)]), (2, [(3,)]),
                       (2, '12'), (2, ['12']), (2, [(0,)])]:
            with self.assertRaises(ValueError):
                parity_query_refute(n, raw)
            self.assertFalse(check_parity_query(n, raw, {}))


if __name__ == '__main__':
    unittest.main()
