import itertools
import random
import unittest
from functools import reduce
from operator import xor

from pnp_lab.graphic_support import (decide_graphic_supports, graphic_difference_basis,
                                     verify_graphic_certificate)
from pnp_lab.ternary_support import three_cnf_to_ternary_supports


def raw_sums(groups):
    return {reduce(xor, choice, 0) for choice in itertools.product(*groups)}


class GraphicSupportTests(unittest.TestCase):
    def check_answer(self, groups, rhs, **kwargs):
        out = decide_graphic_supports(groups, rhs, **kwargs)
        if out['status'] == 'UNKNOWN':
            self.assertIsNone(out['witness'])
        else:
            self.assertEqual(out['status'] == 'SAT', rhs in raw_sums(groups))
        if out['status'] == 'SAT':
            w = out['witness']
            self.assertEqual(len(w), len(groups))
            self.assertTrue(all(x in g for g,x in zip(groups,w)))
            self.assertEqual(reduce(xor,w,0),rhs)
        if out['certificate']:
            self.assertTrue(verify_graphic_certificate(groups,out['certificate']))
        return out

    def test_dense_hidden_units_and_all_targets(self):
        a,b,c = 7,56,448
        shift = 1<<1000
        groups = [[shift ^ v for v in (0,a,b)],(0,b,c),(a,b,c)]
        for v in raw_sums([(0,a),(0,b),(0,c)]):
            got = self.check_answer(groups,shift ^ v)
            self.assertNotEqual(got['status'],'UNKNOWN')
            self.assertEqual(got['rank'],3)
        no = self.check_answer([[shift,shift ^ a,shift ^ b]],shift ^ a ^ b)
        self.assertEqual((no['status'],no['matching_calls']),('UNSAT',1))
        self.assertEqual(self.check_answer(groups,shift ^ 8)['reason'],'outside_affine_hull')

    def test_complete_graph_on_nonpath_branching_basis_tree(self):
        # All rank-5 tree path masks from the five designated edges. Their
        # pairwise adjacency constraints identify where a subdivided claw branches.
        edges = [(0,1),(0,2),(0,3),(3,4),(4,5)]
        potentials = [0,1,2,4,4^8,4^8^16]
        paths = [a ^ b for a,b in itertools.combinations(potentials,2)]
        groups = [(0, x) for x in paths]+[(0,1,2)]
        self.assertEqual(graphic_difference_basis(groups),(1,2,4,8,16))
        auto = decide_graphic_supports(groups,10,max_tree_trials=3)
        self.assertEqual((auto['status'],auto['tree_method']),('SAT','forced_adjacencies'))
        by_cert = decide_graphic_supports(groups,10,basis_edges=edges,max_tree_trials=0)
        self.assertEqual((by_cert['status'],by_cert['tree_trials']),('SAT',0))
        self.assertTrue(verify_graphic_certificate(groups,auto['certificate']))
        with self.assertRaises(ValueError):
            decide_graphic_supports(groups,10,basis_edges=[(0,i+1) for i in range(5)])

    def test_prufer_branch_and_finite_budget(self):
        groups = [(0,1),(0,2),(0,4),(0,8),(0,11)]
        small = self.check_answer(groups,11,max_tree_trials=3)
        self.assertEqual((small['status'],small['reason']),('UNKNOWN','tree_trial_budget_exhausted'))
        large = self.check_answer(groups,11,max_tree_trials=200)
        self.assertEqual((large['status'],large['tree_method']),('SAT','prufer'))
        self.assertGreater(large['tree_trials'],3)

    def test_all_binary_column_subsets_at_rank_at_most_three(self):
        # At rank 3 the 7 nonzero vectors are Fano. Leaving out any one
        # point gives a representation as the 6 edges of K4 (or a restriction).
        for subset in range(1<<7):
            groups = [(0,j+1) for j in range(7) if subset >> j & 1]
            result = self.check_answer(groups,0,max_tree_trials=32)
            self.assertEqual(result['status'],'UNKNOWN' if subset==127 else 'SAT')
            if subset==127:
                self.assertEqual(result['reason'],'too_many_distinct_edges')
        # The edge-count shortcut does not catch a Fano restriction + coloop.
        groups = [(0,j) for j in range(1,9)]
        out = self.check_answer(groups,0,max_tree_trials=200)
        self.assertEqual(out['reason'],'no_graphic_representation')
        self.assertEqual(out['status'],'UNKNOWN')  # the all-zero witness exists

    def test_tiny_real_reduction_obstruction_is_not_unsat(self):
        # Basis contains three value edges and three selector edges.
        # Three selector edges must form a star. The three value edges must
        # form a path and each meets its selector edge, impossible in a tree.
        reduction = three_cnf_to_ternary_supports(('x',),[(1,1,1)])
        self.assertIn(0,raw_sums(reduction.supports))
        r = decide_graphic_supports(reduction.supports,0,max_tree_trials=17000)
        self.assertEqual((r['reason'],r['status'],r['rank']),('no_graphic_representation','UNKNOWN',6))

    def test_raw_selection_oracle_random(self):
        rng = random.Random(341785)
        matches = 0
        for _ in range(90):
            groups = [tuple(rng.sample(range(16),rng.randint(1,3))) for _ in range(rng.randrange(1,7))]
            r = self.check_answer(groups,rng.randrange(16),max_tree_trials=160)
            matches += r['matching_calls']
        self.assertGreater(matches,15)

    def test_boundary_and_invalid_certificates(self):
        self.assertEqual(self.check_answer([],0,max_tree_trials=0)['witness'],[])
        self.assertEqual(self.check_answer([],1)['reason'],'outside_affine_hull')
        self.assertEqual(self.check_answer([(),(1,)],0)['reason'],'empty_support')
        self.assertEqual(self.check_answer([(6,6),(7,)],1,max_tree_trials=0)['witness'],[6,7])
        for args in (([(0,1,2,3)],0),([[],(True,)],0),([],-1)):
            with self.assertRaises(ValueError):
                decide_graphic_supports(*args)
        with self.assertRaises(ValueError):
            decide_graphic_supports([],0,max_tree_trials=False)
        for cert in ({}, {'basis_vectors':[True,2],'basis_edges':[(0,1),(1,2)]},
                     {'basis_vectors':[1,2],'basis_edges':[(0,1),(1,0)]},
                     {'basis_vectors':[1,2],'basis_edges':[(0,1),(1,3)]}):
            with self.assertRaises(ValueError):
                verify_graphic_certificate([(0,1,2)],cert)
