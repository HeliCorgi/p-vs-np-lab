import itertools
import random
import unittest
from functools import reduce
from operator import xor

from pnp_lab.gauge_matching import (decide_with_gauge_matching, partition_radius_one,
                                    radius_one_center)
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


class GaugeMatchingTests(unittest.TestCase):
    def test_center_and_partition_against_exhaustive_ball_oracle(self):
        # At least two distinct options exclude a centre outside their ambient cube:
        # an extra 1 bit consumes the entire radius before reaching any such option.
        centers = range(8)
        for flags in range(1 << 8):
            support = tuple(v for v in range(8) if flags & (1 << v))
            allowed = {c for c in centers if all((x ^ c).bit_count() <= 1 for x in support)}
            got = radius_one_center(support)
            self.assertEqual(got is not None, bool(allowed))
            if got is not None:
                self.assertIn(got, allowed)
            pieces = partition_radius_one(support)
            self.assertEqual(sorted(x for p in pieces for x in p.options), list(support))
            for p in pieces:
                self.assertTrue(all((x ^ p.center).bit_count() <= 1 for x in p.options))
            if len(support) <= 3:
                best = min(len(cs) for k in range(4) for cs in itertools.combinations(centers,k)
                           if all(any((x ^ c).bit_count() <= 1 for c in cs) for x in support))
                self.assertEqual(len(pieces),best)
        # Diameter two alone suffices for three options, but may fail for four.
        self.assertIsNone(radius_one_center((0,3,5,6)))
        self.assertEqual(len(partition_radius_one((0,7,56))),3)
        self.assertEqual(len(partition_radius_one((0,1,14))),2)

    def check_witness(self, result, groups, rhs):
        w = result['witness']; c = result['centers']; u = result['translated_witness']
        self.assertEqual(len(w),len(groups))
        self.assertTrue(all(x in g for x,g in zip(w,groups)))
        self.assertEqual(reduce(xor,w,0),rhs)
        self.assertEqual(u,[x ^ b for x,b in zip(w,c)])
        self.assertTrue(all(x.bit_count() <= 1 for x in u))
        self.assertEqual(reduce(xor,u,0),result['translated_rhs'])
        self.assertEqual(result['translated_rhs'],rhs ^ reduce(xor,c,0))

    def test_raw_product_oracle_with_signed_shifts_and_multiple_outer_branches(self):
        rng = random.Random(8894163)
        for _ in range(400):
            width = rng.randrange(1,6)
            groups = [[rng.randrange(1 << width) for _ in range(rng.randrange(1,5))]
                      for _ in range(rng.randrange(1,6))]
            rhs = rng.randrange(1 << width)
            valid = any(reduce(xor,c,0) == rhs for c in itertools.product(*groups))
            got = decide_with_gauge_matching(groups, rhs)
            self.assertEqual(got['status'], 'SAT' if valid else 'UNSAT', (groups,rhs))
            if valid:
                self.check_witness(got,groups,rhs)
            else:
                self.assertIsNone(got['witness'])
                self.assertEqual(got['outer_branches_total'],got['outer_branches_checked'])
                self.assertEqual(got['branches_total'],got['raw_branches_ruled_out']+got['matching_calls'])
            self.assertLessEqual(got['matching_calls'],got['compatible_branches_identified'])

    def test_high_bits_dense_translations_single_call(self):
        b = (1 << 2048) ^ (1 << 1027) ^ 48
        c = (1 << 1633) ^ 62
        groups = [[b ^ x for x in (0,1,2,4,8)], [c ^ x for x in (2,8,16)]]
        rhs = b ^ c ^ 1 ^ 16
        result = decide_with_gauge_matching(groups,rhs,max_matching_calls=1)
        self.assertEqual((result['status'],result['defect_groups'],result['matching_calls']),('SAT',0,1))
        self.check_witness(result,groups,rhs)

    def test_partial_and_exact_budgets(self):
        groups = [(0,7),(0,1,2,4)]
        # The first binary selector requires the unreachable star option 7.
        # Both selectors pass the affine quotient test: it is only necessary.
        for cap, status in ((0,'UNKNOWN'),(1,'UNKNOWN'),(2,'SAT')):
            r = decide_with_gauge_matching(groups,7,max_matching_calls=cap)
            self.assertEqual((r['status'],r['matching_calls']), (status,cap))
            self.assertEqual((r['branches_total'], r['max_binary_rank']), (2,0))
            if status == 'SAT': self.check_witness(r,groups,7)
            else: self.assertIsNone(r['witness'])
        # Independent outer cap can stop even a sequence of linear contradictions.
        g = [(0,7,56)]
        r = decide_with_gauge_matching(g,1,max_outer_branches=2,max_matching_calls=0)
        self.assertEqual((r['status'],r['reason'],r['outer_branches_checked'],r['matching_calls']),
                         ('UNKNOWN','outer_branch_budget_exhausted',2,0))
        r = decide_with_gauge_matching(g,1,max_outer_branches=3,max_matching_calls=0)
        self.assertEqual((r['status'],r['raw_branches_ruled_out'],r['matching_calls']),('UNSAT',3,0))
        r = decide_with_gauge_matching([(0,7)],2,max_matching_calls=0)
        self.assertEqual((r['status'],r['outer_branches_inconsistent']),('UNSAT',1))

    def test_rank_filter_on_actual_cycle_bridge(self):
        # On these 2-CNF formulas every repeated variable contributes one copy
        # selector per occurrence, but equality parity leaves just one free bit per variable.
        for n in (3,4):
            clauses = []
            for j in range(n):
                a,b = j+1,(j+1)%n+1
                clauses.extend(((a,b),(-a,-b)))
            red = three_cnf_to_weight_two_supports([str(i) for i in range(n)],clauses)
            r = decide_with_gauge_matching(red.supports,red.rhs)
            self.assertEqual(r['binary_defects'],4*n)
            self.assertEqual(r['nonbinary_defects'],0)
            self.assertEqual(r['max_binary_rank'],3*n)
            self.assertEqual(r['branches_total'],2**(4*n))
            self.assertEqual(r['compatible_branches_identified'],2**n)
            if n == 3:
                self.assertEqual((r['status'],r['matching_calls']),('UNSAT',2**n))
            else:
                self.assertEqual(r['status'],'SAT')
                self.assertIn(red.project_witness(r['witness']), (5,10))

    def test_degenerate_and_invalid(self):
        self.assertEqual(decide_with_gauge_matching([],5)['status'],'UNSAT')
        r = decide_with_gauge_matching([],0,max_outer_branches=0,max_matching_calls=0)
        self.check_witness(r,[],0)
        self.assertEqual(decide_with_gauge_matching([[],(1,)],0)['status'],'UNSAT')
        for groups, target, opts in (([[],[True]],0,{}), ([(1,)],False,{}),
                                     ([(-2,)],0,{}),([],0,{'max_outer_branches':-1}),
                                     ([],0,{'max_matching_calls':True}), ('',0,{})):
            with self.assertRaises(ValueError):
                decide_with_gauge_matching(groups,target,**opts)
        with self.assertRaises(ValueError): radius_one_center([True])
