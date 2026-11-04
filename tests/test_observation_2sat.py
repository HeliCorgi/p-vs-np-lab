import itertools
import random
import unittest

from pnp_lab.observation_2sat import solve_observation_2sat
from pnp_lab.selector_events import compile_compact_events


def oracle(n,events):
    return {x for x in range(1<<n) if not any(all((x&m).bit_count()%2==b for m,b in e) for e in events)}


class ObservationTests(unittest.TestCase):
    def compare(self,n,events,**opts):
        points=oracle(n,events);r=solve_observation_2sat(n,events,**opts)
        self.assertEqual(r['status'],'SAT' if points else 'UNSAT')
        if points:self.assertIn(r['witness'],points)
        else:self.assertIsNone(r['witness'])
        self.assertEqual(r['distinct_forms']-r['rank'],r['deficiency'])
        self.assertEqual(len(r['parity_checks']),r['deficiency'])
        self.assertEqual(r['common_basis'],r['deficiency']==0)
        return r

    def test_raw_point_oracles_and_both_closure_outcomes(self):
        rng=random.Random(78271);reasons=set()
        for _ in range(420):
            n=rng.randrange(1,7);events=[]
            for _ in range(rng.randrange(1,15)):
                point=rng.randrange(1<<n);ms=[rng.randrange(1,1<<n) for _ in range(rng.choice((1,2,2,2)))]
                events.append([(m,(m&point).bit_count()%2) for m in ms])
            reasons.add(self.compare(n,events)['reason'])
        self.assertEqual(reasons,{'consistent_2sat_model','parity_feasible_implication_closure',
                                  'boolean_2sat_relaxation_unsat','degree_bounded_closures_exhausted'})

    def test_recognition_against_all_ambient_bases_in_dimension_three(self):
        lines=range(1,8)
        planes=sorted({tuple(sorted((a,b,a^b))) for a,b in itertools.combinations(lines,2)})
        bases=[set(b) for b in itertools.combinations(lines,3) if b[0]^b[1]^b[2]]
        for mask in range(1<<7):
            used=[p for i,p in enumerate(planes) if mask>>i&1]
            for units in (set(),{1},{1,2,3},{3,5}):
                events=[[(p[0],0),(p[1],1)] for p in used]+[[(m,1)] for m in units]
                want=any(units<=b and all(len(b.intersection(p))==2 for p in used) for b in bases)
                got=solve_observation_2sat(3,events,max_subsets=0)
                self.assertEqual(got['common_basis'],want,(used,units))
                if want:self.assertNotEqual(got['status'],'UNKNOWN')

    def test_hidden_signed_axes_and_scc_unsat_without_enumeration(self):
        a,b,c=3,5,12
        events=[[(a^b,1),(b,0)],[(b^c,0),(c,1)],[(a,1)]]
        self.assertTrue(self.compare(4,events,max_subsets=0)['common_basis'])
        bad=[[(a^b,i^j),(b,j)] for i,j in itertools.product(range(2),repeat=2)]
        self.assertEqual(self.compare(4,bad,max_subsets=0)['reason'],'boolean_2sat_relaxation_unsat')

    def test_budget_boundary_and_nontrivial_recovered_model(self):
        cases=([((6,0),(1,1)),((4,0),(5,1)),((2,0),(6,1)),((3,1),(1,0))],
               [((4,0),(6,1)),((4,1),(5,1)),((7,0),(2,0)),((6,0),(1,1))])
        for es,reason in zip(cases,('parity_feasible_implication_closure','degree_bounded_closures_exhausted')):
            r=self.compare(3,es);n=r['subsets_tested'];self.assertGreater(n,1);self.assertEqual(r['reason'],reason)
            self.compare(3,es,max_subsets=n)
            z=solve_observation_2sat(3,es,max_subsets=n-1)
            self.assertEqual((z['status'],z['witness']),('UNKNOWN',None))

    def test_positive_deficiency_is_not_claimed_minimum(self):
        # Forced private edge lines on a four-cycle. Exactly a vertex cover
        # of the original coordinate lines must be added; optimum size 4+2.
        edges=[(0,1),(0,3),(1,2),(2,3)]
        ev=[[(1<<i,0),(1<<j,0)] for i,j in edges]+[[((1<<i)^(1<<j),1)] for i,j in edges]
        r=self.compare(4,ev)
        self.assertEqual(r['distinct_forms'],7)
        self.assertFalse(r['common_basis'])
        covers=[c for c in range(16) if all((c>>i | c>>j)&1 for i,j in edges)]
        self.assertEqual(4+min(c.bit_count() for c in covers),6)

    def test_compact_selector_source_agreement_and_edge_inputs(self):
        for cs in ([(1,-2,3),(-1,2,-3)],[(1,),(-1,)],[(1,1,-2)],[],[()]):
            e=compile_compact_events(('a','b','c'),cs)
            ans=self.compare(e.n_parameters,e.events)
            if ans['status']=='SAT':e.project_witness(ans['witness'])
        for n,ev in ((0,[]),(0,[[]]),(0,[[(0,1)]]),(3,[[(1,0),(2,1),(3,1)]])):
            self.compare(n,ev)
        for n,es in ((-1,[]),(2,[[(1,2)]]),(0,[[],[(1,1)]]),(3,[[(1,0),(2,0),(4,1)]])):
            with self.assertRaises(ValueError):solve_observation_2sat(n,es)
        with self.assertRaises(ValueError):solve_observation_2sat(1,[],max_subsets=-1)
