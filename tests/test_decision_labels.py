import random
import unittest
from itertools import product

from pnp_lab.decision_labels import canonical_cnf, or_cnf, residual_label


def satisfies(f, x):
    return all(any(bool(x & 1 << (abs(l)-1)) == (l>0) for l in c) for c in f)


def label_holds(k, x):
    if k == ('YES',): return True
    if k == ('NO',): return False
    if k[0] == 'CNF': return satisfies(k[1],x)
    return satisfies(k[1],x) and all((x & a).bit_count()%2==b for a,b in k[2])


class DecisionLabelTests(unittest.TestCase):
    def test_projected_core_has_exact_named_image_before_blocking(self):
        rng=random.Random(11391)
        n=6
        for case in range(130):
            f=[]
            for _ in range(rng.randrange(6)):
                vs=rng.sample(range(1,n+1),rng.randrange(1,5)); b=rng.randrange(2)
                for t in product((0,1),repeat=len(vs)):
                    if sum(t)%2==b:f.append(tuple(-v if z else v for v,z in zip(vs,t)))
            for _ in range(case%5):
                f.append(tuple(v*rng.choice((-1,1)) for v in rng.sample(range(1,n+1),3)))
            k=residual_label(n,f)
            mask=0
            if k[0]=='CORE':
                for c in k[1]:
                    for l in c:mask |= 1 << (abs(l)-1)
            expected={x & mask for x in range(1<<n) if satisfies(f,x)}
            actual={x & mask for x in range(1<<n) if label_holds(k,x)}
            self.assertEqual(actual,expected)
            blocked=residual_label(n,f,mode='blocked')
            self.assertEqual(any(label_holds(blocked,x) for x in range(1<<n)),bool(expected))

    def test_same_coordinate_or_including_constants(self):
        rng=random.Random(1108)
        for _ in range(150):
            def formula():
                return [[rng.choice((-1,1))*rng.randrange(1,5) for _ in range(rng.randrange(4))]
                        for _ in range(rng.randrange(6))]
            a,b=formula(),formula()
            f=or_cnf(4,a,b)
            self.assertEqual([satisfies(f,x) for x in range(16)],
                             [satisfies(a,x) or satisfies(b,x) for x in range(16)])

    def test_equal_keys_never_identify_yes_and_no_on_all_two_bit_formulas(self):
        clauses=[(1,),(-1,),(2,),(-2,)]+[(a,b) for a in (1,-1) for b in (2,-2)]
        for mode in ('syntax','affine','blocked'):
            known={}
            for mask in range(1<<len(clauses)):
                f=[c for i,c in enumerate(clauses) if mask>>i&1]
                k=residual_label(2,f,mode=mode)
                sat=any(satisfies(f,x) for x in range(4))
                self.assertEqual(known.setdefault(k,sat),sat)
