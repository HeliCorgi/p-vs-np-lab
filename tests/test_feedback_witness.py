from itertools import product
import unittest

from pnp_lab.feedback_fixture import feedback_case
from pnp_lab.feedback_witness import feedback_witness, check_feedback_witness
from pnp_lab.ternary_flow import scramble


def parity(par):
    return [tuple((-1 if b else 1)*(i+1) for i, b in enumerate(t))
            for t in product(range(2), repeat=3) if sum(t) % 2 != par]


class FeedbackWitnessTests(unittest.TestCase):
    def test_known_family_both_signs_no_planted_hint(self):
        for bad in (False, True):
            n, rows, word, _ = feedback_case(6, bad, layers=3)
            raw, planted = scramble(n, rows, word, 1771)
            q = feedback_witness(n, (r for r in raw))
            if bad:
                self.assertEqual(q['status'], 'UNKNOWN')
                self.assertIsNone(q['witness'])
            else:
                self.assertEqual(q['status'], 'SAT')
                self.assertTrue(check_feedback_witness(n, raw, q['witness']))
                self.assertTrue(check_feedback_witness(n, raw, planted))
                self.assertEqual(q['stats']['scc_calls'], 1)
                self.assertEqual(q['stats']['raw_clauses_checked'], len(raw))
                v = abs(raw[0][0])
                anti = -v if q['witness'] >> (v-1) & 1 else v
                self.assertFalse(check_feedback_witness(n, ((anti,),)+raw, q['witness']))

    def test_one_rejected_proposal_need_not_mean_unsat(self):
        # Even parity chooses x=y=z=0; a nonanchor unit g mandates x=1
        # through (not g or x). The valid global model x=y=g=1,z=0 exists.
        rows = parity(0) + [(4,), (-4, 1)]
        self.assertTrue(check_feedback_witness(4, rows, 11))
        out = feedback_witness(4, rows)
        self.assertEqual(out['status'], 'UNKNOWN')
        self.assertEqual(out['stats']['scc_calls'], 1)
        self.assertIsNone(out['witness'])

    def test_nonparity_empty_projection_and_resource_preflight(self):
        for rows in ([], [(1, 2, 3)], [(1, 2, 3), (-1, -2, -3)]):
            self.assertEqual(feedback_witness(3, rows)['status'], 'UNKNOWN')
        n, cs, w, _ = feedback_case(4, False, layers=2)
        for limits in (dict(max_active=0), dict(max_clauses=1), dict(max_word_bits=0),
                       dict(max_lemmas=0), dict(max_edges=0), dict(max_path_steps=0)):
            q = feedback_witness(n, cs, **limits)
            self.assertEqual(q['status'], 'UNKNOWN')
            self.assertTrue(q['stats']['budget_limited'])
        q = feedback_witness(10**12, [(10**12,)], max_word_bits=100)
        self.assertEqual(q['reason'], 'original word bit cap')
        rows = parity(1) + [(4, 5), (-5, 4)] * 4
        q = feedback_witness(5, rows, max_edges=2)
        self.assertEqual(q['reason'], 'residual arc cap')
        self.assertIsNone(q['witness'])
        for x in (True, -1, 1 << n, [w]):
            self.assertFalse(check_feedback_witness(n, cs, x))
