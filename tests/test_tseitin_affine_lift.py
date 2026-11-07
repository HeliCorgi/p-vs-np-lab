"""Independent finite oracles for Tseitin gate graph and affine lifting."""
import unittest

from tseitin_affine_lift import build_cnf, eval_clause, extension, positive, verify


class TseitinAffineLiftTests(unittest.TestCase):
    def test_and_xor_gate_truth_tables_independently(self):
        for a in (0,1):
            for b in (0,1):
                for c in (0,1):
                    bits = a | b << 1 | c << 2
                    and_cnf = ((-3,1),(-3,2),(3,-1,-2))
                    xor_cnf = ((1,2,-3),(1,-2,3),(-1,2,3),(-1,-2,-3))
                    self.assertEqual(all(eval_clause(k,bits) for k in and_cnf),
                                     c == (a & b))
                    self.assertEqual(all(eval_clause(k,bits) for k in xor_cnf),
                                     c == (a ^ b))

    def test_full_extended_space_exhaustive(self):
        for m in (1,2,3):
            n, clauses, _ = build_cnf(m)
            observed = {z for z in range(1<<n)
                        if all(eval_clause(c,z) for c in clauses)}
            truth = set()
            for x in range(1<<m):
                for y in range(1<<m):
                    if sum((x>>i & 1)*(y>>i & 1) for i in range(m))%2 == 1:
                        truth.add(extension(m,x | (y<<m)))
            self.assertEqual(observed, truth)
            self.assertEqual(len(observed),(2**m-1)*2**(m-1))

    def test_independent_plane_counts(self):
        expected = [(1,1,1,1),(2,21,21,3),(3,721,541,7)]
        for m, old, new, cover in expected:
            got = verify(m)
            self.assertEqual(got['original_positive_flats'],old)
            self.assertEqual(got['affine_flats_after_tseitin_lift'],new)
            self.assertEqual(got['explicit_affine_cover'],cover)
            self.assertEqual(got['clauses'],7*m-3)
            self.assertEqual(got['variables'],4*m-1)

    def test_counterexample_positive_plane_does_not_lift_affinely(self):
        m=3
        plane = []
        for u in (0,1):
            for v in (0,1):
                x = 1 | u<<1 | u<<2
                y = 1 | v<<1 | v<<2
                z = x | y<<m
                self.assertTrue(positive(m,z))
                plane.append(z)
        self.assertEqual(plane[0]^plane[1]^plane[2]^plane[3],0)
        self.assertNotEqual(extension(m,plane[0]) ^ extension(m,plane[1]) ^
                            extension(m,plane[2]) ^ extension(m,plane[3]), 0)
        # Both individual nonaffine AND outputs p_1 and p_2 become uv.
        residue = extension(m,plane[0]) ^ extension(m,plane[1]) ^ \
                  extension(m,plane[2]) ^ extension(m,plane[3])
        self.assertEqual(residue & (1<<(2*m+1)), 1<<(2*m+1))
        self.assertEqual(residue & (1<<(2*m+2)), 1<<(2*m+2))

    def test_committed_report_is_reproducible(self):
        import json
        from pathlib import Path
        target = Path(__file__).resolve().parents[1] / 'results' / 'tseitin_affine_lift.json'
        report = json.loads(target.read_text(encoding='utf-8'))
        self.assertEqual(report['results'], json.loads(json.dumps([verify(m) for m in (1,2,3)])))

    def test_budget_and_m1_edges(self):
        with self.assertRaises(ValueError): verify(0)
        with self.assertRaises(ValueError): verify(4)
        with self.assertRaises(ValueError): build_cnf(0)
        n, clauses, gates = build_cnf(1)
        self.assertEqual((n,len(clauses),gates),(3,4,()))


if __name__=='__main__':
    unittest.main()
