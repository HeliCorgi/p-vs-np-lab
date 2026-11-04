import unittest
from copy import deepcopy
from itertools import combinations,permutations
from math import gcd
from pnp_lab.prime_spectrum import check_local_spectrum,discover_prime_spectrum,spectrum_table


def exact_det(rows):
    n=len(rows);total=0
    for p in permutations(range(n)):
        v=-1 if sum(a>b for i,a in enumerate(p) for b in p[i+1:])%2 else 1
        for i,j in enumerate(p):v*=rows[i][j]
        total+=v
    return total


class PrimeSpectrumTests(unittest.TestCase):
    def test_all_three_bit_tables_by_gcd_of_all_full_minors(self):
        for table in range(256):
            words=[w for w in range(8) if table>>w&1]
            rank=0;divisor=1
            for r in range(min(4,len(words)),0,-1):
                g=0
                for ws in combinations(words,r):
                    for cols in combinations(range(4),r):
                        g=gcd(g,exact_det([[1 if j==3 else w>>j&1 for j in cols] for w in ws]))
                        if g==1:break
                    if g==1:break
                if g:rank,divisor=r,g;break
            q=spectrum_table(3,table)
            self.assertEqual(q['rational']['rank'],rank)
            # 4x4 0/1 minor has |det|≤16; all possible primes covered.
            self.assertEqual(q['exceptional_primes'],[p for p in (2,3,5,7,11,13) if divisor%p==0])
            # Raw 3-CNF encodes precisely this table, independent of Gaussian code.
            raw=[tuple(-(j+1) if w>>j&1 else j+1 for j in range(3)) for w in range(8) if not table>>w&1]
            self.assertTrue(check_local_spectrum(3,raw,[1,2,3],q))

    def test_modular_rank_witness_and_rational_minor_tampering(self):
        cs=[tuple(-j if w>>(j-1)&1 else j for j in (1,2,3)) for w in range(8) if w.bit_count()%2]
        q=spectrum_table(3,sum(1<<w for w in range(8) if not w.bit_count()%2))
        self.assertEqual(q['exceptional_primes'],[2])
        for how in ('prime','rank','word','minor','subset'):
            t=deepcopy(q)
            if how=='prime':t['exceptional_primes']=[]
            if how=='rank':t['modular']['2']['rank']+=1
            if how=='word':t['rational']['words'][0]=1
            if how=='minor':t['rational']['minor']+=1
            if how=='subset':del t['modular']['2']
            self.assertFalse(check_local_spectrum(3,cs,(1,2,3),t))
        # A 1x1 true minor is a lower bound but not an upper bound.
        t=deepcopy(q);t.update(rational=dict(rank=1,columns=[3],words=[0],minor=1),modular={},exceptional_primes=[])
        self.assertFalse(check_local_spectrum(3,cs,(1,2,3),t))

    def test_scope_cap_zero_and_empty(self):
        r=discover_prime_spectrum(4,[(1,2,3)],max_scopes=0)
        self.assertFalse(r['complete_for_scopes']);self.assertEqual(r['primes'],[])
        r=discover_prime_spectrum(0,[()]);self.assertEqual((r['empty_scopes'],r['primes']),(1,[]))
        self.assertTrue(check_local_spectrum(0,[()],[],spectrum_table(0,0)))
        with self.assertRaises(ValueError):spectrum_table(10,0)
        with self.assertRaises(ValueError):discover_prime_spectrum(1,[],max_scopes=-1)
