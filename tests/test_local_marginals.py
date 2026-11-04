import copy
import json
from pathlib import Path
import unittest

from pnp_lab.local_marginals import check_local_marginals, linear_triple_marginals
from pnp_lab.modular_barrier import check_preorder, line_fixture


class LocalMarginalTests(unittest.TestCase):
    def test_unsat_and_sat_twins_both_have_checked_level_four_distributions(self):
        n, raw = line_fixture(0)
        raw = raw[:152]
        saved = json.loads((Path(__file__).resolve().parents[1]
                            / 'results/modular_barrier.json').read_text())
        self.assertTrue(check_preorder(n, raw, saved['fixture']['tree_preorder']))
        positive = tuple(tuple(map(abs, c)) for c in raw)
        for cs in (raw, positive):
            out = linear_triple_marginals(n, cs)
            self.assertEqual(out['status'], 'UNKNOWN')
            self.assertEqual(out['relaxation'], 'FEASIBLE')
            self.assertTrue(check_local_marginals(n, cs, out['certificate']))
            stats = out['stats']
            self.assertTrue(stats['complete'])
            self.assertFalse(stats['budget_limited'])
            self.assertEqual(stats['scopes_checked'], 36457)
            self.assertEqual(stats['table_states_checked'], 541323)
            self.assertEqual(stats['positive_states'], 506667)
            self.assertEqual(stats['projection_equalities_checked'], 1062711)

    def test_all_clause_signs_and_nonconsecutive_original_labels(self):
        for signs in range(8):
            clause = tuple(-v if signs >> j & 1 else v for j, v in enumerate((2, 4, 7)))
            cs = [clause, (1, -3, 7)]
            out = linear_triple_marginals(8, cs)
            self.assertEqual(out['relaxation'], 'FEASIBLE')
            self.assertTrue(check_local_marginals(8, cs, out['certificate']))
            wrong = copy.deepcopy(out['certificate'])
            wrong['clause_parities'][0] ^= 1
            self.assertFalse(check_local_marginals(8, cs, wrong))

    def test_unsupported_inputs_cannot_acquire_a_feasibility_claim(self):
        for cs in ([()], [(1,)], [(1, 2)], [(1, 1, 2)], [(1, -1, 2)],
                   [(1, 2, 3), (-1, -2, 4)], [(1, 2, 3), (-1, 2, 3)]):
            out = linear_triple_marginals(4, cs)
            self.assertEqual(out['status'], 'UNKNOWN')
            self.assertEqual(out['relaxation'], 'UNKNOWN')
            self.assertIsNone(out['certificate'])
            self.assertFalse(out['stats']['complete'])
        empty = linear_triple_marginals(0, [])
        self.assertEqual(empty['relaxation'], 'FEASIBLE')
        self.assertEqual(empty['stats']['scopes_checked'], 1)
        self.assertEqual(empty['status'], 'UNKNOWN')

    def test_certificate_tampering_and_strict_types(self):
        n, cs = 4, [(1, -2, 3)]
        cert = linear_triple_marginals(n, cs)['certificate']
        for key, value in [('kind', 'other'), ('variables', True), ('variables', 3),
                           ('level', 5), ('level', True), ('clause_parities', []),
                           ('clause_parities', [True]), ('clause_parities', [2])]:
            bad = copy.deepcopy(cert)
            bad[key] = value
            self.assertFalse(check_local_marginals(n, cs, bad), (key, value))
        changed = [(-1, -2, 3)]
        self.assertFalse(check_local_marginals(n, changed, cert))
        self.assertFalse(check_local_marginals(n, cs, None))

    def test_caps_reject_without_claiming_infeasibility_or_allocating_ambient_space(self):
        good = linear_triple_marginals(3, [(1, 2, 3)])['certificate']
        for kwargs in (dict(max_states=0), dict(max_checks=0)):
            out = linear_triple_marginals(3, [(1, 2, 3)], **kwargs)
            self.assertEqual(out['status'], 'UNKNOWN')
            self.assertEqual(out['relaxation'], 'UNKNOWN')
            self.assertIsNone(out['certificate'])
            self.assertTrue(out['stats']['budget_limited'])
            self.assertEqual(out['stats']['scopes_checked'], 0)
            self.assertFalse(check_local_marginals(3, [(1, 2, 3)], good, **kwargs))
        huge = 10**12
        out = linear_triple_marginals(huge, [(1, 2, huge)])
        self.assertTrue(out['stats']['budget_limited'])
        self.assertEqual(out['stats']['table_states_checked'], 0)
        for key in ('max_states', 'max_checks'):
            for value in (True, -1, 0.5):
                with self.assertRaises(ValueError):
                    linear_triple_marginals(0, [], **{key: value})


if __name__ == '__main__':
    unittest.main()
