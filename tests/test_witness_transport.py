from itertools import product,combinations
import random
import unittest

from pnp_lab.witness_transport import (KIND,find_transport,find_flip_transport,
                                       check_transport,apply_transport)


def holds(cs,w):
    return all(any(bool(w & 1<<(abs(v)-1))==(v>0) for v in c) for c in cs)


def clauses_for(positions,words):
    return [tuple(-j if w>>i&1 else j for i,j in enumerate(positions)) for w in words]


def flip(n,t):
    return {'kind':KIND,'images':[-(i+1) if t>>i&1 else i+1 for i in range(n)]}


class WitnessTransportTests(unittest.TestCase):
    def test_raw_independent_checker_and_direction(self):
        # Non-injective substitution: target y2 and y3 are opposite copies of x1.
        c={'kind':KIND,'images':[False,1,-1,True],'method':'untrusted nonsense'}
        a=[(1,),(4,-4)]
        b=[(1,2),(2,3),(-1,-4),(-1,3),(4,),(2,2)]
        self.assertTrue(check_transport(4,a,b,c))
        for w in range(16):
            if holds(a,w):self.assertTrue(holds(b,apply_transport(4,c,w)))
        self.assertFalse(check_transport(4,[(-1,)],b,c))
        self.assertFalse(check_transport(4,a,b,dict(c,images=[False,-1,-1,True])))
        for bad in (None,{}, dict(c,kind='guess'),dict(c,images=[1]*3),dict(c,images=[0]*4),
                    dict(c,images=[5]*4),dict(c,images=[1.0]*4)):
            self.assertFalse(check_transport(4,a,b,bad))
        self.assertTrue(check_transport(0,[()],[()],flip(0,0)))
        self.assertFalse(check_transport(0,[],[()],flip(0,0)))
        with self.assertRaises(ValueError): apply_transport(4,c,16)
        with self.assertRaises(ValueError): find_transport(2,[(True,)],[])
        with self.assertRaises(ValueError): find_transport(2,[],[(1,)]*2,strategies=['unsound'])

    def test_equal_profile_translation_with_global_dependencies(self):
        rng=random.Random(119058)
        for n in range(1,9):
            for _ in range(12):
                a=[tuple(v*rng.choice((1,-1)) for v in rng.sample(range(1,n+1),min(n,3)))
                   for _ in range(15)]
                planted=flip(n,rng.randrange(1<<n))
                b=[tuple((planted['images'][abs(v)-1])*(1 if v>0 else -1)
                         for v in c) for c in a]
                t=find_flip_transport(n,a,b)
                self.assertIsNotNone(t);self.assertTrue(check_transport(n,a,b,t))
                for w in range(1<<n):
                    if holds(a,w):self.assertTrue(holds(b,apply_transport(n,t,w)))
        # Global orientation is pinned across 137 bits. Enumerating all flips is infeasible.
        n=137;a=[(1,)];b=[(-1,)]
        for j in range(1,n):
            a+=clauses_for((j,j+1),(1,2))
            b+=clauses_for((j,j+1),(0,3))
        t=find_flip_transport(n,a,b)
        self.assertEqual(t['images'],[-(i+1) if i%2==0 else i+1 for i in range(n)])

    def test_subsumption_is_directional_and_syntactically_checkable(self):
        a=[(1,)];b=[(1,2)]
        t=find_flip_transport(2,a,b)
        self.assertIsNotNone(t)
        self.assertIsNone(find_flip_transport(2,b,a))
        # A chosen variable fold creates a tautological target clause.
        t=find_transport(3,[(1,)],[(1,-3),(2,3),(-2,-3)],strategies=('single',))
        self.assertIsNotNone(t);self.assertTrue(check_transport(3,[(1,)],[(1,-3),(2,3),(-2,-3)],t))
        for f in ((1,2),(-1,-2)):
            c=find_transport(2,[],[f],strategies=('constants',))
            self.assertTrue(holds([f],apply_transport(2,c,0)))

    def test_certified_global_bijunctive_horn_dualhorn_search(self):
        def run(blocks,n,method):
            a=[c for vs,s in blocks for c in clauses_for(vs,s)]
            b=[vs for vs,s in blocks]
            t=find_flip_transport(n,a,b)
            self.assertIsNotNone(t)
            self.assertEqual(t['method'],method)
            self.assertTrue(check_transport(n,a,b,t))
        run([((1,2,3),[1,2,3])],3,'translate-2sat')
        run([((1,2,3),set(range(8))-{3}),((1,4,5),[1,3,5,7]),
             ((2,6,7),[1,3,5,7])],7,'translate-horn')
        run([((1,2,3),set(range(8))-{4}),((3,4,5),[1,3,5,7])],5,'translate-dual-horn')

    def test_arbitrary_maps_correspond_to_real_model_transports(self):
        rng=random.Random(121212)
        for _ in range(320):
            n=4
            form=lambda:[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in
                               range(rng.randrange(4))) for _ in range(rng.randrange(8))]
            a,b=form(),form()
            cert={'kind':KIND,'images':[rng.choice([False,True,-1,1,-2,2,-3,3,-4,4]) for _ in range(n)]}
            for t in (cert,find_transport(n,a,b),find_flip_transport(n,a,b)):
                if t is not None and check_transport(n,a,b,t):
                    for w in range(1<<n):
                        if holds(a,w):self.assertTrue(holds(b,apply_transport(n,t,w)))

    def test_three_uniform_two_colorability_is_exact_diagonal_obligation(self):
        # Fano plane: each source edge must be monochromatic. A shift works
        # semantically AND syntactically iff every edge of the shift is mixed.
        edges={tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,8),2)}
        for skip in (False,True):
            e=sorted(edges)[int(skip):]
            a=[c for p in e for c in clauses_for(p,range(1,7))]; b=e
            models=[w for w in range(128) if holds(a,w)]
            self.assertEqual(models,[0,127])
            good=[]
            for w in range(128):
                mixed=all(0<sum((w>>(i-1))&1 for i in edge)<3 for edge in e)
                self.assertEqual(check_transport(7,a,b,flip(7,w)),mixed)
                self.assertEqual(all(holds(b,x^w) for x in models),mixed)
                if mixed:good.append(w)
            self.assertEqual(bool(good),skip)
            self.assertIsNotNone(find_transport(7,a,b,strategies=('constants',)))


if __name__=='__main__':unittest.main()
