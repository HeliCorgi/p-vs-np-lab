import copy
import random
import unittest

from pnp_lab.conservation import solve_conservation, check_conservation
from pnp_lab.integer_hull import integer_hull_refute
from pnp_lab.integer_probe import (integer_probe_refute, check_integer_probe,
                                   guarded_disjunction)
from pnp_lab.ternary_flow import prism_flow, scramble


def holds(cs, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs)


class IntegerProbeTests(unittest.TestCase):
    def test_blind_root_conditional_refutation_and_independent_replay(self):
        n, f, _ = prism_flow(4, bad=True, modulus=2)
        m, g, _ = prism_flow(4, bad=True)
        v, cs, _, _ = guarded_disjunction(n, f, m, g)
        cs, _ = scramble(v, cs, None, 15015)
        root = integer_hull_refute(v, cs)
        self.assertEqual(root['status'], 'UNKNOWN')
        self.assertTrue(root['stats']['scope_complete'])
        self.assertEqual(root['stats']['local_rows'], 0)
        out = solve_conservation(v, cs, method='integer-probe', max_integer_calls=3)
        self.assertEqual(out['status'], 'UNSAT')
        self.assertTrue(check_conservation(v, cs, out))
        proof = out['certificate']
        self.assertEqual(len(proof['deductions']), 1)
        moduli = [proof['deductions'][0]['proof']['integer']['modulus'],
                  proof['terminal']['integer']['modulus']]
        self.assertEqual(set(moduli), {2, 3})
        for change in ('flip', 'drop', 'repeat', 'future', 'steps', 'integer'):
            bad = copy.deepcopy(proof)
            if change == 'flip':
                bad['deductions'][0]['assume'] *= -1
            elif change == 'drop':
                bad['deductions'] = []
            elif change == 'repeat':
                bad['deductions'] *= 2
            elif change == 'future':
                bad['deductions'][0]['proof'] = bad['terminal']
            elif change == 'steps':
                bad['deductions'][0]['proof']['steps'][0][2] = -1
            else:
                bad['terminal']['integer']['terms'] = []
            self.assertFalse(check_integer_probe(v, cs, bad), change)

    def test_caps_never_make_a_decision_and_sat_arms_have_raw_models(self):
        n, f, fw = prism_flow(3, bad=False, modulus=2)
        m, g, gw = prism_flow(3, bad=False)
        for arm in ('left', 'right'):
            v, cs, word, _ = guarded_disjunction(n, f, m, g,
                left_word=fw if arm == 'left' else None,
                right_word=gw if arm == 'right' else None)
            cs, word = scramble(v, cs, word, 15099)
            self.assertTrue(holds(cs, word))
            q = integer_probe_refute(v, cs, max_calls=4)
            self.assertEqual(q['status'], 'UNKNOWN')
            self.assertTrue(q['stats']['budget_limited'])
            self.assertFalse(check_integer_probe(v, cs, q['certificate']))
        q = integer_probe_refute(1, [(1,), (-1,)], max_calls=0)
        self.assertEqual((q['status'], q['stats']['integer_calls']), ('UNKNOWN', 0))
        for cap in (-1, True, 0.5):
            with self.assertRaises(ValueError):
                integer_probe_refute(0, [], max_calls=cap)

    def test_random_small_formula_soundness_and_zero_step_original_ids(self):
        rng = random.Random(150708)
        for _ in range(35):
            n = rng.randint(1, 5)
            cs = [tuple(rng.choice((-1, 1)) * rng.randint(1, n)
                        for _ in range(rng.randint(1, 3))) for _ in range(rng.randrange(14))]
            # Includes duplicate literals, tautologies and empty raw formulas.
            sat = any(holds(cs, w) for w in range(1 << n))
            r = integer_probe_refute(n, cs, max_calls=6)
            if r['status'] == 'UNSAT':
                self.assertFalse(sat)
                self.assertTrue(check_integer_probe(n, cs, r['certificate']))
            else:
                self.assertEqual(r['status'], 'UNKNOWN')
                self.assertIsNone(r['certificate'])
        cs = [(1, -1), (1,), (-1,)]
        r = integer_probe_refute(1, cs, private_peel=False)
        self.assertEqual(r['status'], 'UNSAT')
        self.assertTrue(check_integer_probe(1, cs, r['certificate']))
        self.assertFalse(check_integer_probe(1, [(1, -1), (1,), (1,)], r['certificate']))
