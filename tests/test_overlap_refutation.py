from copy import deepcopy
from itertools import combinations, product
import random
import unittest

from pnp_lab.overlap_refutation import refute_affine_cover, verify_cover_certificate


def event_holds(event,w):
    return all((m&w).bit_count()%2==b for m,b in event)


def raw_identity(evs, terms, w):
    return sum(event_holds(evs[i], w) and (w&z)==z for i,z in terms)%2


class StaticCertificateTests(unittest.TestCase):
    def test_exhaustive_arrangements_in_two_dimensions_at_full_degree(self):
        # Every distinct nonempty affine flat in F_2^2, including the whole plane.
        flats = [()] + [((m,b),) for m in (1,2,3) for b in (0,1)]
        flats += [((1,a),(2,b)) for a,b in product(range(2),repeat=2)]
        for mask in range(1<<len(flats)):
            ev = [e for j,e in enumerate(flats) if mask>>j & 1]
            covered = all(any(event_holds(e,w) for e in ev) for w in range(4))
            ans = refute_affine_cover(2,ev,degree=2)
            self.assertEqual(ans['status'], 'UNSAT' if covered else 'UNKNOWN')
            if covered:
                self.assertTrue(all(raw_identity(ev,ans['certificate']['terms'],w) for w in range(4)))
                self.assertTrue(verify_cover_certificate(2,ev,ans['certificate'],max_degree=2))

    def test_higher_degree_can_certify_overlap_missed_by_low_degree(self):
        ev=[[(1,0),(2,0)],[(1,0),(2,1)],[(1,1),(2,0)],[(1,1),(4,0)],[(2,1),(4,1)]]
        low=refute_affine_cover(3,ev,degree=2)
        self.assertEqual((low['status'],low['reason']),('UNKNOWN','constant_not_in_bounded_span'))
        high=refute_affine_cover(3,ev,degree=3)
        self.assertEqual(high['certificate']['degree'],3)
        self.assertTrue(all(raw_identity(ev,high['certificate']['terms'],w) for w in range(8)))
        self.assertEqual(refute_affine_cover(3,ev[:-1],degree=3)['status'],'UNKNOWN')

    def test_seeded_arbitrary_parities_and_redundant_equations(self):
        rng=random.Random(119109)
        for _ in range(130):
            n=rng.randrange(5)
            ev=[[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,6))]
                for _ in range(rng.randrange(9))]
            if ev: ev[0]=ev[0]*2
            covered=all(any(event_holds(e,w) for e in ev) for w in range(1<<n))
            ans=refute_affine_cover(n,ev,degree=n)
            self.assertEqual(ans['status']=='UNSAT',covered)
            if covered:
                self.assertTrue(all(raw_identity(ev,ans['certificate']['terms'],w) for w in range(1<<n)))

    def test_budget_boundaries_and_high_rank_filter_before_expansion(self):
        self.assertEqual(refute_affine_cover(0,[[]],degree=0,max_rows=0)['reason'],'row_budget_exhausted')
        self.assertEqual(refute_affine_cover(0,[[]],degree=0,max_rows=1)['status'],'UNSAT')
        ev=[[(1<<i,0) for i in range(200)],[(0,1)],[(1,0)],[(1,1)]]
        limited=refute_affine_cover(10**8,ev,degree=2,max_rows=1)
        self.assertEqual((limited['status'],limited['active_variables'],limited['events_above_degree'],
                          limited['impossible_events']),('UNKNOWN',1,1,1))
        self.assertEqual(refute_affine_cover(10**8,ev,degree=2,max_rows=2)['status'],'UNSAT')
        self.assertEqual(refute_affine_cover(1,[[(1,1)]],degree=1,max_rows=1)['reason'],'constant_not_in_bounded_span')

    def test_tampered_or_incorrect_degree_certificates_rejected(self):
        ev=[[(1,0),(1,0),(0,0)],[(1,1)],[(1,0),(1,1)]]
        c=refute_affine_cover(1,ev,degree=3)['certificate']
        self.assertEqual(c['degree'],1)
        for key,val in [('kind','unsupported'),('n',True),('degree',0),('degree',2),
                        ('terms',[]),('terms',[[0,0]]),('terms',[[0,0],[1,0],[2,0]]),
                        ('terms',[[0,0],[0,0],[1,0]]),('terms',[[0,-1]]),('terms',[[0,2]]),
                        ('terms',[[True,0]]),('terms',[[0,True]]),('terms',[[10,0]])]:
            bad=deepcopy(c);bad[key]=val
            with self.assertRaises(ValueError):verify_cover_certificate(1,ev,bad)
        with self.assertRaises(ValueError):verify_cover_certificate(1,ev,c,max_degree=0)

    def test_validates_even_unvisited_events(self):
        for ev in ([[], [(2,0)]],[[],[(True,1)]],[[],[(0,True)]],[[],[(-1,0)]],['']):
            with self.assertRaises(ValueError):refute_affine_cover(1,ev,degree=0)
        for opts in ({'degree':-1},{'max_rows':False}):
            with self.assertRaises(ValueError):refute_affine_cover(1,[],**opts)
        with self.assertRaises(ValueError):refute_affine_cover(True,[])
