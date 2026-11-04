"""Independent point oracles, coordinate changes, budgets and all-size families."""
import itertools
import random
import unittest
from pnp_lab.overlap_lattice import solve_affine_arrangement


def good(n,events):
    return {x for x in range(1<<n)
            if not any(all(((x&m).bit_count()&1)==b for m,b in event) for event in events)}


class ArrangementTests(unittest.TestCase):
    def compare(self,n,events,**opts):
        answer=solve_affine_arrangement(n,events,**opts)
        expected=good(n,events)
        self.assertEqual(answer['survivor_count'],len(expected), (n,events,opts))
        self.assertEqual(answer['status'],'SAT' if expected else 'UNSAT')
        if expected:self.assertIn(answer['witness'],expected)
        else:self.assertIsNone(answer['witness'])
        return answer

    def test_small_point_oracle_and_noncoordinate_slices(self):
        rng=random.Random(990173)
        for _ in range(350):
            n=rng.randrange(1,7); events=[]
            for _ in range(rng.randrange(1,11)):
                at=rng.randrange(1<<n); ms=[rng.randrange(1,1<<n) for _ in range(rng.choice([1,2,2,2,3]))]
                events.append([(m,(m&at).bit_count()&1) for m in ms])
            self.compare(n,events)
            self.compare(n,events,condition_on=[rng.randrange(1<<n),rng.randrange(1<<n)])

    def test_redundancy_contradictions_and_free_dimensions(self):
        a=self.compare(5,[[(1,0),(2,1)],[(3,1),(2,1)],[(1,0),(2,1),(4,0)],[(5,0),(5,1)]])
        self.assertEqual((a['duplicate_events'],a['contained_events'],a['impossible_events']),(1,1,1))
        self.assertEqual(self.compare(0,[])['witness'],0)
        self.assertEqual(self.compare(0,[[]])['survivor_count'],0)
        self.assertEqual(solve_affine_arrangement(199,[[(1,1)]])['survivor_count'],1<<198)
        a=self.compare(4,[[(3,1)],[(3,0),(12,1)]],max_intersections=0)
        self.assertEqual(a['forced_rank_added'],2)
        with self.assertRaises(ValueError):solve_affine_arrangement(2,[[],[(4,0)]])
        with self.assertRaises(ValueError):solve_affine_arrangement(2,[[(1,2)]])
        with self.assertRaises(ValueError):solve_affine_arrangement(2,[],condition_on=[4])
        for name in ('max_slices','max_intersections'):
            with self.assertRaises(ValueError):solve_affine_arrangement(0,[],**{name:True})

    def test_noncoordinate_factorization(self):
        # Four independent masks; coordinates overlap in the original encoding.
        coords=(0b1011,0b1101,0b0111,0b1110)
        ev=[[(coords[0],0),(coords[1],0)],[(coords[2],1),(coords[3],0)]]
        ans=self.compare(6,ev)
        self.assertEqual(ans['max_components_per_slice'],2)
        self.assertEqual(ans['survivor_count'],3*3*4)

    def test_signed_merging_of_many_axes(self):
        n=10
        ev=[[(1<<j,0) for j in range(n) if i!=j] for i in range(n)]
        a=self.compare(n,ev)
        self.assertEqual(a['peak_terms'],n+2)
        self.assertEqual(a['intersections_tested'],(n*n+3*n-4)//2)
        self.assertEqual(a['survivor_count'],(1<<n)-n-1)
        self.assertEqual(a['component_count'],1)

    def test_connected_path_has_exponential_final_terms(self):
        # Internal gaps keep intersections unique on an induced matching.
        for n in (3,6,9,12):
            ev=[[(1<<i,0),(1<<(i+1),0)] for i in range(n-1)]
            a=self.compare(n,ev)
            self.assertEqual(a['component_count'],1)
            self.assertGreaterEqual(a['peak_terms'],1<<(n//3))
        a=solve_affine_arrangement(60,[[(1<<i,0),(1<<(i+1),0)] for i in range(59)],max_intersections=96)
        self.assertEqual((a['status'],a['survivor_count'],a['witness'],a['intersections_tested']),
                         ('UNKNOWN',None,None,96))

    def test_budget_including_exact_completion_edge(self):
        ev=[[(1,0),(2,0)],[(2,0),(4,0)],[(1,1),(4,1)]]
        total=self.compare(3,ev)['intersections_tested']
        self.assertGreater(total,0)
        self.compare(3,ev,max_intersections=total)
        a=solve_affine_arrangement(3,ev,max_intersections=total-1)
        self.assertEqual((a['reason'],a['survivor_count']),('intersection_budget_exhausted',None))
        self.compare(3,ev,condition_on=(3,5,6,0),max_slices=4)
        a=solve_affine_arrangement(3,ev,condition_on=(3,5,6,0),max_slices=3)
        self.assertEqual((a['slices_total'],a['slices_completed'],a['status'],a['witness']),(4,3,'UNKNOWN',None))

    def test_identical_bounded_order_cardinalities_do_not_decide_coverage(self):
        n=4;z=1<<n
        ev=lambda b: [[(1<<i,0),(z,s)] for i in range(n) for s in (0,1)]+[[(z-1,b),(z,s)] for s in (0,1)]
        ea,eb=ev(0),ev(1)
        sets=lambda es:[set(range(2*z))-good(n+1,[e]) for e in es]
        pa,pb=sets(ea),sets(eb)
        for k in range(1,n+1):
            for idx in itertools.combinations(range(len(ea)),k):
                self.assertEqual(len(set.intersection(*(pa[j] for j in idx))),len(set.intersection(*(pb[j] for j in idx))))
        self.assertEqual(self.compare(n+1,ea)['survivor_count'],0)
        self.assertEqual(self.compare(n+1,eb)['survivor_count'],2)
