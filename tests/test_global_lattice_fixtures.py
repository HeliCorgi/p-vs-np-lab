import unittest

from pnp_lab.global_lattice_fixtures import carry_cycle, carry_gate, carry_field_values
from pnp_lab.local_torsion import local_torsion, check_local_torsion
from pnp_lab.modular_hull import discover_scopes
from pnp_lab.ternary_flow import scramble


def models(n, clauses):
    return [x for x in range(1 << n)
            if all(any(bool(x >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in clauses)]


class GlobalLatticeFixtureTests(unittest.TestCase):
    def test_gate_truth_table_and_saturated_lattice(self):
        for carry in (0, 1):
            cs = carry_gate(1, 2, 3, carry)
            self.assertEqual(models(3, cs), [w for w in range(8)
                if (w & 1) + ((w >> 1) & 1) - ((w >> 2) & 1) == carry])
            profile = local_torsion(3, cs, (1, 2, 3))
            self.assertEqual(profile['torsion'], [])
            self.assertEqual(profile['free_rank'], 1)
            self.assertTrue(check_local_torsion(3, cs, (1, 2, 3), profile['certificate']))

    def test_exact_small_family_and_blinded_sat_siblings(self):
        for m in range(2, 5):
            for total in range(m+1):
                n, cs, word, meta = carry_cycle(m, total, wire_length=1)
                found = models(n, cs)
                self.assertEqual(bool(found), total in (0, m))
                self.assertEqual(len(cs), 4*m + 2*(2*m-1))
                self.assertEqual(sum(meta['carries']), total)
                if word is not None:
                    self.assertIn(word, found)
                    raw, renamed = scramble(n, cs, word, 15993+m)
                    self.assertIn(renamed, models(n, raw))
        for m, total, length in ((1, 0, 10), (4, 5, 10), (4, 2, 0)):
            with self.assertRaises(ValueError):
                carry_cycle(m, total, wire_length=length)

    def test_prime_relaxations_and_all_discovered_local_profiles(self):
        for m, total in ((4, 2), (5, 1), (7, 1), (8, 2), (9, 3)):
            n, cs, _, meta = carry_cycle(m, total)
            for p in (2, 3, 5, 7, 11):
                point = carry_field_values(n, meta, p)
                self.assertEqual(point is not None, m % p != 0 or total % p == 0)
            raw, _ = scramble(n, cs, None, 15134+m)
            for scope in discover_scopes(n, raw):
                result = local_torsion(n, raw, scope)
                self.assertEqual(result['status'], 'PROFILE')
                self.assertEqual(result['torsion'], [])


if __name__ == '__main__':
    unittest.main()
