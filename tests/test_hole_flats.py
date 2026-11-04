import itertools
import random
import unittest
from functools import reduce
from operator import xor

from pnp_lab.hole_flats import decide_hole_flats
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


class HoleFlatTests(unittest.TestCase):
    def checked(self, groups, rhs, expect_decided=False):
        answer=decide_hole_flats(groups,rhs)
        possible=any(reduce(xor,p,0)==rhs for p in itertools.product(*groups))
        if answer['status']=='UNKNOWN':
            self.assertFalse(expect_decided)
            self.assertIsNone(answer['witness'])
        else:
            self.assertEqual(answer['status'],'SAT' if possible else 'UNSAT')
        if answer['status']=='SAT':
            w=answer['witness']
            self.assertEqual(len(w),len(groups))
            self.assertTrue(all(x in g for x,g in zip(w,groups)))
            self.assertEqual(reduce(xor,w,0),rhs)
        return answer

    def test_every_translated_pair_of_triangles_in_three_bits(self):
        # In dimension three, two planes intersect in at least a line.
        triples=list(itertools.combinations(range(8),3))
        for i,a in enumerate(triples):
            for b in triples[i:]:
                for rhs in range(8):
                    got=self.checked((a,b),rhs,True)
                    self.assertEqual(got['merges'],1)

    def test_seeded_choices_and_witnesses(self):
        rng=random.Random(42283)
        for _ in range(320):
            g=[tuple(rng.sample(range(16),rng.choice([1,2,3,3,3]))) for _ in range(rng.randrange(8))]
            rhs=(reduce(xor,(rng.choice(s) for s in g),0) if rng.randrange(2) else rng.randrange(32))
            self.checked(g,rhs)

    def test_non_graphic_difference_set_and_exact_full_flat(self):
        gs=((0,1,2),(0,1,4),(0,1,6))
        self.assertEqual({x^y for g in gs for x,y in itertools.combinations(g,2)},set(range(1,8)))
        for rhs in range(8):
            ans=self.checked(gs,rhs,True)
            self.assertEqual(ans['full_merges'],1)
            self.assertEqual(ans['split_nodes'],2)

    def test_dense_symbolic_result_with_one_missing_point(self):
        m=140
        gs=[(0,1,1<<j) for j in range(1,m+1)]
        missing=(1<<(m+1))-1
        bad=decide_hole_flats(gs,missing)
        self.assertEqual((bad['status'],bad['reason'],bad['max_flat_rank']),('UNSAT','forced_hole',m+1))
        ok=decide_hole_flats(gs,missing^1)
        self.assertEqual(ok['status'],'SAT')
        self.assertEqual(ok['witness'],[1<<j for j in range(1,m+1)])
        ok=decide_hole_flats(gs+[(0,1,6)],missing)
        self.assertEqual((ok['status'],ok['full_merges']),('SAT',1))

    def test_direct_sum_and_nonunique_decomposition(self):
        gs=[(0,1,2),(0,4,8)]
        self.assertEqual(self.checked(gs,5,True)['merges'],0)
        self.assertEqual(self.checked(gs,3,True)['reason'],'forced_hole')
        # Pairwise disjoint but not jointly direct: do not declare a false UNSAT.
        gs=gs+[(0,5,10)]
        r=[self.checked(gs,v) for v in range(16)]
        self.assertTrue(any(x['status']=='UNKNOWN' for x in r))
        self.assertTrue(any(x['status']=='SAT' for x in r))

    def test_affine_presolve_original_recovery_and_empty_cases(self):
        for rhs in range(16):
            self.checked(((7,12),(3,5,6),(10,11,15)),rhs)
        for g,t in (([],0),([],3),([[]],0),([(5,)],5),([(7,7,2)],2)):
            self.checked(g,t,True)
        for g,t in (([(True,)],0),([(0,1,2,3)],0),([[],[-1]],0),([],False)):
            with self.assertRaises(ValueError):
                decide_hole_flats(g,t)

    def test_optional_cover_constructs_missing_diagonal_witnesses(self):
        gs=[(0,1,2),(0,4,8),(0,5,10)]
        cover_uses=0
        for rhs in range(16):
            base=decide_hole_flats(gs,rhs)
            ans=decide_hole_flats(gs,rhs,cover=True)
            self.assertEqual(ans['status'],'SAT')
            self.assertEqual(reduce(xor,ans['witness'],0),rhs)
            self.assertTrue(all(v in g for v,g in zip(ans['witness'],gs)))
            if base['status']=='UNKNOWN':
                cover_uses+=1
                ev=ans['cover_evidence']
                self.assertEqual((ev['total_decompositions'],ev['bad_counts'],ev['exclusion_sum']),
                                 (4,[1,1,1],3))
                self.assertEqual(ev['reason'],'conditional_cover_witness')
        self.assertEqual(cover_uses,7)

    def test_signed_cube_actual_sparse_encoding_stalls(self):
        f=[[(j+1)*s for j,s in enumerate(ss)] for ss in itertools.product((-1,1),repeat=3)]
        r=three_cnf_to_weight_two_supports(('x','y','z'),f)
        result=decide_hole_flats(r.supports,r.rhs)
        self.assertEqual((result['status'],result['affine_groups'],result['merges'],
                          result['final_flats'],result['decomposition_nullity']),
                         ('UNKNOWN',24,0,32,19))
        cov=decide_hole_flats(r.supports,r.rhs,cover=True)
        self.assertEqual(cov['status'],'UNKNOWN')
        self.assertEqual(cov['cover_evidence']['bad_counts'],[1<<17]*32)
