from copy import deepcopy
from itertools import combinations,permutations
from math import gcd
import unittest
from pnp_lab.local_torsion import check_local_torsion,local_torsion,torsion_table,scan_local_torsion


def perm_det(ws,cols):
    ans=0
    for perm in permutations(cols):
        v=-1 if sum(a>b for i,a in enumerate(perm) for b in perm[i+1:])%2 else 1
        for w,c in zip(ws,perm):v*=1 if c==3 else w>>c&1
        ans+=v
    return ans


class LocalTorsionTests(unittest.TestCase):
    def test_all_three_bit_truth_tables_by_determinantal_divisors(self):
        for table in range(256):
            words=[w for w in range(8) if table>>w&1]
            prior=1;ds=[]
            for j in range(1,min(len(words),4)+1):
                g=0
                for ws in combinations(words,j):
                    for cols in combinations(range(4),j):
                        g=gcd(g,perm_det(ws,cols))
                        if g==prior:break
                    if g==prior:break
                if not g:break
                ds.append(g//prior);prior=g
            c=torsion_table(3,table)['certificate']
            self.assertEqual(c['diagonal'],ds)
            f=[tuple(v*(-1 if w>>(v-1)&1 else 1) for v in (1,2,3)) for w in range(8) if w not in words]
            self.assertTrue(check_local_torsion(3,f,(1,2,3),c))

    def test_caps_and_empty_relation_are_not_trivial_torsion_assertions(self):
        self.assertEqual(torsion_table(3,255,max_models=3)['status'],'UNKNOWN')
        self.assertEqual(torsion_table(3,255,max_ops=0)['status'],'UNKNOWN')
        self.assertEqual(torsion_table(3,255,max_bits=0)['status'],'UNKNOWN')
        with self.assertRaises(ValueError):torsion_table(16,0)
        c=local_torsion(3,[()],(1,2,3))
        self.assertEqual((c['status'],c['models'],c['rank']),('PROFILE',0,0))
        self.assertTrue(check_local_torsion(3,[()],(1,2,3),c['certificate']))
        self.assertEqual(scan_local_torsion(0,[()])['scanned_scopes'],0)

    def test_tampered_trace_and_unimodularity(self):
        n=3;rows=[tuple(j*(-1 if w>>(j-1)&1 else 1) for j in (1,2,3)) for w in range(8) if w.bit_count()%2]
        cert=local_torsion(n,rows,[1,2,3])['certificate']
        self.assertEqual(cert['diagonal'][-1],2)
        for op in (['r',0,0,1],['C',0,4],['scale',0,2],['N',False]):
            bad=deepcopy(cert);bad['ops'].insert(0,op)
            self.assertFalse(check_local_torsion(n,rows,[1,2,3],bad))
        bad=deepcopy(cert);bad['diagonal'][-1]=1;self.assertFalse(check_local_torsion(n,rows,[1,2,3],bad))
        self.assertFalse(check_local_torsion(n,rows[:-1],[1,2,3],cert))
