import random
import unittest
from itertools import product
from functools import reduce
from operator import xor
from pnp_lab.event_projection import project_affine_events
from pnp_lab.fiber_arrangement import compile_flat_arrangement,solve_flat_arrangement
from pnp_lab.selector_events import compile_selector_events


class ProjectionTests(unittest.TestCase):
    def test_random_both_orders_against_raw_points(self):
        rng=random.Random(427113)
        for _ in range(240):
            n=rng.randrange(0,7)
            es=[[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(1,4))]
                for _ in range(rng.randrange(10))]
            good={x for x in range(1<<n) if not any(all((x&a).bit_count()%2==b for a,b in e) for e in es)}
            order=list(range(n));rng.shuffle(order)
            for o in (order,None):
                r=project_affine_events(n,es,order=o)
                self.assertEqual(r['status'],'SAT' if good else 'UNSAT')
                if good:self.assertIn(r['witness'],good)

    def test_bad_union_projection_grid_and_budget(self):
        for k in range(2,7):
            zs=(1<<k)-1
            es=[[(zs,0)]]+[[(1<<i,1),(1<<(k+2*i+j),0)] for i in range(k) for j in range(2)]
            r=project_affine_events(3*k,es,order=range(3*k))
            self.assertEqual(r['status'],'SAT')
            self.assertGreaterEqual(r['layer_sizes'][k]*2**k,3**k)
        e=[[(1,0),(2,0)],[(1,1),(4,0)]]
        self.assertEqual(project_affine_events(3,e,order=[0,1,2],max_pairs=0)['status'],'UNKNOWN')

    def test_cube_signed_source_and_near_miss(self):
        cs=[[(-i if mask>>(i-1)&1 else i) for i in [1,2,3]] for mask in range(8)]
        for clauses,sat in ((cs,False),(cs[1:],True)):
            enc=compile_selector_events(['a','b','c'],clauses)
            order=[*range(3,enc.n_parameters),0,1,2]
            r=project_affine_events(enc.n_parameters,enc.events,order=order)
            self.assertEqual(r['status'],'SAT' if sat else 'UNSAT')
            if sat:self.assertEqual(enc.project_witness(r['witness']),0)

    def test_flats_bijective_on_decompositions(self):
        rng=random.Random(31871)
        for _ in range(60):
            n=rng.randrange(1,5); fs=[]; raw=[]
            for j in range(rng.randrange(0,5)):
                a=rng.randrange(1<<n); ds=tuple(1<<i for i in rng.sample(range(n),rng.randrange(min(n,2)+1)))
                pts={reduce(xor,(d for i,d in enumerate(ds) if k>>i&1),a) for k in range(1<<len(ds))}
                h=rng.choice([None,*sorted(pts)]);fs.append((a,ds,h));raw.append(pts-{h})
            t=rng.randrange(1<<n); good={q for q in product(*raw) if reduce(xor,q,0)==t}
            f=compile_flat_arrangement(fs,t); decoded=set()
            if f.particular is not None:
                for p in range(1<<f.dimension):
                    if not any(all((p&a).bit_count()%2==b for a,b in e) for e in f.events):
                        decoded.add(tuple(f.decode(p)))
            self.assertEqual(decoded,good)
            r=solve_flat_arrangement(fs,t)
            self.assertEqual(r['status'],'SAT' if good else 'UNSAT')
            if good:self.assertIn(tuple(r['witness']),good)

    def test_unsatisfiable_and_whole_events_before_shortcuts(self):
        self.assertEqual(project_affine_events(0,[[]])['status'],'UNSAT')
        self.assertEqual(project_affine_events(0,[[(0,1)]])['status'],'SAT')
        with self.assertRaises(ValueError):project_affine_events(1,[[],[(2,1)]])
        with self.assertRaises(ValueError):project_affine_events(5,[],order=[0,1])
