import copy
import unittest
from pnp_lab.integer_hull import check_integer_hull
from pnp_lab.one_column_feedback import one_column_certificate


def tables(m, q):
    rows = []
    for i in range(m):
        tr = (i+1, m+1, 1+(i+1)%m)
        c = ((i+1)*q)//m - (i*q)//m
        for w in range(8):
            x,y,z = tuple((w >> j) & 1 for j in range(3))
            if x+y-z != c:
                rows.append(tuple(-v if w>>j&1 else v for j,v in enumerate(tr)))
    return rows


class OneColumnTests(unittest.TestCase):
    def test_all_small_charges_against_raw_truth_and_replay(self):
        for m in range(3,8):
            for q in range(m+1):
                cs = tables(m, q)
                sat = any(all(any(bool(word >> (abs(l)-1) & 1) == (l>0) for l in c)
                              for c in cs) for word in range(1 << (m+1)))
                cert, _ = one_column_certificate(m+1, cs)
                self.assertEqual(cert is None, sat)
                if cert:
                    self.assertTrue(check_integer_hull(m+1, cs, cert))
                    self.assertEqual(cert['modulus'], m)
                    self.assertTrue(all(abs(t['weight']) == 1 for t in cert['terms']))

    def test_malformed_proof_and_resource_limit(self):
        cs = tables(4, 2)
        cert, _ = one_column_certificate(5, cs)
        bad = copy.deepcopy(cert)
        bad['terms'][0]['weight'] *= -1
        self.assertFalse(check_integer_hull(5, cs, bad))
        cert, stats = one_column_certificate(5, cs, max_bits=1)
        self.assertIsNone(cert)
        self.assertTrue(stats['budget_limited'])
        self.assertIsNone(one_column_certificate(5, [(1,2,3)])[0])
