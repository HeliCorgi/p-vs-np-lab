from fractions import Fraction as Q
from itertools import product
from math import comb
import unittest

from experiments.soft_partition_path import (AuditBudgetExceeded, dyadic,
    evaluate_cnf, evaluate_histogram, matched_jet_control, parameters, path,
    ratio_interval, value_and_moments)


class SoftPartitionPathTests(unittest.TestCase):
    def test_weighted_moments_against_direct_assignment_evaluation(self):
        clauses = [(1, 2), (-1, 3), (-2,), (1, 2)]
        energies = [sum(not any(bits[abs(x)-1] == (x>0) for x in clause)
                        for clause in clauses) for bits in product((False,True),repeat=3)]
        histogram = [energies.count(j) for j in range(5)]
        for q in (Q(1), Q(2,3), Q(1,32)):
            total, moments = value_and_moments(histogram,q,6)
            direct = sum(q**e for e in energies)
            self.assertEqual(total,direct)
            self.assertEqual(moments,[sum(comb(e,j)*q**e for e in energies if e>=j)/direct
                                      for j in range(7)])

    def test_all_four_assignment_histograms_with_perturbed_moments(self):
        for first in product(range(5),repeat=3):
            if sum(first)>4:
                continue
            histogram = list(first)+[4-sum(first)]
            for q in (Q(1),Q(1,2),Q(1,16)):
                total, moments = value_and_moments(histogram,q,4)
                error = Q(1,10000)
                noisy = [Q(1)]+[v+(-1)**j*error for j,v in enumerate(moments[1:],1)]
                for h in (Q(0),Q(1,48),Q(1,24)):
                    lo,hi = ratio_interval(3,noisy,h,error)
                    exact = sum(c*(q*(1-h))**j for j,c in enumerate(histogram))/total
                    self.assertLessEqual(lo,exact)
                    self.assertLessEqual(exact,hi)

    def test_interval_decision_for_extreme_and_mixed_distributions(self):
        for histogram in ([4],[0,4],[0,0,0,4],[1,0,0,3],[2,1,1],[0,2,2]):
            row = evaluate_histogram(2,histogram,noisy=True)
            self.assertEqual(row['status'],'SAT' if histogram[0] else 'UNSAT')
            self.assertLessEqual(row['steps'],row['step_bound'])
        self.assertEqual(evaluate_cnf(0,[])['status'],'SAT')
        self.assertEqual(evaluate_cnf(0,[()])['status'],'UNSAT')

    def test_path_endpoint_step_radius_and_polynomial_bound(self):
        for n,m in product(range(4),range(1,6)):
            p=parameters(n,m)
            steps=list(path(n,m))
            self.assertLessEqual(len(steps),p['step_bound'])
            self.assertEqual(steps[0][0],1)
            self.assertEqual(steps[-1][1],p['target'])
            for q,t in steps:
                self.assertGreater(q,t)
                self.assertLessEqual(q-t,q/(8*m))
            self.assertGreaterEqual(8**(p['order']+1),32*p['step_bound'])

    def test_old_initial_jet_does_not_determine_fresh_moments(self):
        control=matched_jet_control()
        self.assertEqual(control['satisfying_assignments'],[32,0])
        self.assertEqual(control['matching_initial_orders'],list(range(8)))
        self.assertEqual(control['required_initial_order'],6)
        self.assertNotEqual(*control['first_weighted_moment_at_half'])

    def test_budgets_and_invalid_data_do_not_return_a_sat_decision(self):
        with self.assertRaises(AuditBudgetExceeded):
            evaluate_cnf(10,[(1,)],assignment_limit=100)
        with self.assertRaises(AuditBudgetExceeded):
            evaluate_cnf(2,[(1,),(-1,)],step_limit=1)
        for histogram in ([],[0,0],[3],[-1,5]):
            with self.assertRaises(ValueError):
                evaluate_histogram(2,histogram)
        with self.assertRaises(ValueError):
            value_and_moments([1],Q(0),1)
        with self.assertRaises(ValueError):
            ratio_interval(2,[1,0,0],Q(1,2))

    def test_outward_rounding_preserves_exact_bounds(self):
        for numerator in range(-20,21):
            value=Q(numerator,7)
            lo,hi=dyadic(value,5),dyadic(value,5,upper=True)
            self.assertLessEqual(lo,value)
            self.assertLessEqual(value,hi)
            self.assertLess(hi-lo,Q(1,16))


if __name__ == '__main__':
    unittest.main()
