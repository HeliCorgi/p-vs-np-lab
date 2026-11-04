from functools import reduce
from itertools import product
from operator import xor
import random
import unittest

from pnp_lab.flat_cover import solve_hole_cover


def points(a, dirs):
    vals=[a]
    for d in dirs:
        vals += [v^d for v in vals]
    return vals


class HoleCoverTests(unittest.TestCase):
    def test_joint_plane_dependency_invisible_to_pairs(self):
        # A, B and the diagonal of A+B are pairwise disjoint in directions.
        # The joint kernel has dimension two and projects onto each plane.
        flats=[(0,(1,2),0),(0,(4,8),0),(0,(5,10),0)]
        for t in range(16):
            r=solve_hole_cover(flats,t)
            self.assertEqual((r['total_decompositions'],r['bad_counts'],r['projection_ranks']),
                             (4,[1,1,1],[2,2,2]))
            self.assertEqual((r['uniform_strict'],r['uniform_exclusion_bound'],r['status']),
                             (True,3,'SAT'))
            self.assertEqual((r['reason'],r['parameter_steps']),('conditional_cover_witness',2))
            w=r['witness'];self.assertEqual(reduce(xor,w,0),t)
            self.assertTrue(all(v in points(a,ds) and v!=h for v,(a,ds,h) in zip(w,flats)))

    def test_projection_counts_strict_criterion_and_actual_answers_against_raw_oracle(self):
        rng=random.Random(183941)
        for _ in range(210):
            flats=[];hulls=[]
            for _ in range(rng.randrange(1,6)):
                a=rng.randrange(16);ds=rng.sample(range(1,16),k=rng.randrange(3))
                vals=points(a,ds);h=rng.choice(vals) if rng.randrange(3) else None
                flats.append((a,ds,h));hulls.append(vals)
            t=rng.randrange(16)
            fiber=[v for v in product(*hulls) if reduce(xor,v,0)==t]
            good=[v for v in fiber if all(x!=f[2] for x,f in zip(v,flats))]
            r=solve_hole_cover(flats,t)
            self.assertEqual(r['total_decompositions'],len(fiber))
            if not fiber:
                self.assertEqual(r['status'],'UNSAT');continue
            counts=[sum(v[i]==h for v in fiber) for i,(_,_,h) in enumerate(flats)]
            ranks=[None if h is None else len({v[i] for v in fiber}).bit_length()-1
                   for i,(_,_,h) in enumerate(flats)]
            self.assertEqual((r['bad_counts'],r['projection_ranks']),(counts,ranks))
            worst=sum(len(fiber)//(1<<d) for d in ranks if d is not None)
            self.assertEqual(r['uniform_strict'],worst<len(fiber))
            if sum(counts)<len(fiber):self.assertEqual(r['status'],'SAT')
            if r['status']=='SAT':self.assertIn(tuple(r['witness']),good)
            elif r['status']=='UNSAT':self.assertFalse(good)
            else:self.assertIsNone(r['witness'])

    def test_large_kernel_without_enumeration(self):
        k=80
        a=[1<<i for i in range(k)]
        b=[x<<k for x in a]
        diag=[x^y for x,y in zip(a,b)]
        flats=[(0,a,0),(0,b,0),(0,diag,0)]
        r=solve_hole_cover(flats,0)
        self.assertEqual((r['status'],r['total_decompositions'],r['exclusion_sum']),('SAT',1<<k,3))
        self.assertEqual((r['parameter_steps'],r['conditional_rank_tests']),(k,3*k))
        x,y,z=r['witness'];self.assertTrue(x and y and z)
        self.assertEqual(y,x<<k);self.assertEqual(z,x^y)

    def test_inconclusive_bounds_do_not_decide(self):
        flats=[(0,(1,),0),(0,(1,),0)]
        # At 0 a good witness exists, though both forbidden events hit the
        # same parameter. At 1 the events together cover the whole fiber.
        # In neither case is the naive particular witness good.
        for t in (0,1):
            r=solve_hole_cover(flats,t)
            self.assertEqual((r['status'],r['bad_counts'],r['exclusion_sum']),('UNKNOWN',[1,1],2))
            self.assertIsNone(r['witness'])
        # A different target can make all decompositions hit one particular hole.
        flats=[(0,(1,),1),(0,(2,),None),(0,(2,),None)]
        r=solve_hole_cover(flats,1)
        self.assertEqual((r['total_decompositions'],r['bad_counts'],r['status']),(2,[2,0,0],'UNSAT'))
        self.assertEqual(r['reason'],'one_hole_covers_entire_fiber')
        r=solve_hole_cover(flats,0)
        self.assertEqual((r['status'],r['exclusion_sum'],r['uniform_strict']),('SAT',0,False))

    def test_full_flat_empty_product_zero_dimensional_and_input_errors(self):
        for t in (0,1):
            r=solve_hole_cover([],t);self.assertEqual(r['status'],'SAT' if not t else 'UNSAT')
        self.assertEqual(solve_hole_cover([(3,(),3)],3)['status'],'UNSAT')
        self.assertEqual(solve_hole_cover([(3,(),None)],3)['witness'],[3])
        self.assertEqual(solve_hole_cover([(3,(4,),None)],6)['status'],'UNSAT')
        for flats,t in (([(0,(1,2,3),None)],0), ([(0,(1<<99,),1)],1),
                        ([(False,(),None)],0), ([(0,[True],None)],0),
                        ([(0,(),-1)],0), ([(0,())],0), ([],False), ('',0)):
            with self.assertRaises(ValueError):solve_hole_cover(flats,t)
