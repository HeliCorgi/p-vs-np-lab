import copy
import itertools
import random
import unittest
from collections import Counter
from functools import reduce
from operator import xor

from pnp_lab.minor_universality import build_binary_minor,verify_binary_minor
from pnp_lab.ternary_support import three_cnf_to_weight_two_supports


def independent_subset_audit(instance):
    # Work directly on raw option pairs, before presolve. A retained subset
    # is zero in the minor iff its sum is in the span of all contracted pairs.
    # Low-pivot echelon and exhaustive subset membership do not call the
    # compiler's high-pivot dependency/coordinate routines.
    groups=three_cnf_to_weight_two_supports(instance.variables,instance.clauses).supports
    def col(ref):
        g,i,j=ref
        return groups[g][i]^groups[g][j]
    piv={}
    def residual(v):
        while v:
            pivot=v & -v
            if pivot not in piv:return v
            v ^= piv[pivot]
        return 0
    raw=[g[0]^g[1] for g in groups if len(g)==2]
    for v in raw+[col(ref) for ref in instance.certificate['contract']]:
        y=residual(v)
        if y:piv[y & -y]=y
    kept=[col(ref) for ref in instance.certificate['keep']]
    for take in itertools.product((False,True),repeat=len(kept)):
        a=reduce(xor,(x for x,b in zip(instance.columns,take) if b),0)
        b=reduce(xor,(x for x,bit in zip(kept,take) if bit),0)
        if (a==0)!=(residual(b)==0):return False
    return True


class MinorUniversalityTests(unittest.TestCase):
    def check_instance(self,matrix):
        obj=build_binary_minor(matrix)
        self.assertTrue(all(len(c)==len(set(c))==3 and min(c)>0 for c in obj.clauses))
        freq=Counter(x for c in obj.clauses for x in c)
        self.assertEqual(set(freq),set(range(1,len(obj.variables)+1)))
        self.assertTrue(all(x in (2,3) for x in freq.values()))
        self.assertEqual(len(set(obj.designated_clauses)),len(matrix))
        report=verify_binary_minor(obj.supports,matrix,obj.certificate)
        self.assertTrue(report['verified'] and report['presolve']['fixed_point'])
        self.assertEqual(report['presolve']['contracted_rank'],3*len(obj.clauses))
        self.assertTrue(independent_subset_audit(obj))
        return obj,report

    def test_loop_parallel_coloop_and_empty_boundaries(self):
        for cols in [(),(0,),(0,0),(5,), (5,5),(1,1,0,2),(1<<2400,1,(1<<2400)^1)]:
            _,report=self.check_instance(cols)
            self.assertEqual(report['loops'],sum(x==0 for x in cols))

    def test_graphic_and_nongraphic_and_long_relator(self):
        for cols,rank in [((1,2,4,3,5,6,7),3),((11,13,14,1,2,4,8),4),
                          ((1,2,4,8,16,31),5), (tuple((1<<i)^(1<<j) for i,j in itertools.combinations(range(5),2)),4)]:
            self.assertEqual(self.check_instance(cols)[1]['rank'],rank)

    def test_random_labelled_dependencies(self):
        rng=random.Random(712603)
        for _ in range(18):
            cols=tuple(rng.randrange(8) for _ in range(rng.randrange(1,7)))
            self.check_instance(cols)

    def test_checker_not_just_rank_or_unlabelled_isomorphism(self):
        o=build_binary_minor((1,2,3,4))
        # Same labelled ground set size, rank, nullity and abstract matroid,
        # but the circuit moves from (0,1,2) to (0,1,3).
        with self.assertRaisesRegex(ValueError,'labelled retained dependencies'):
            verify_binary_minor(o.supports,(1,2,4,3),o.certificate)
        for key in ('contract','keep'):
            bad=copy.deepcopy(o.certificate);bad[key][0]=bad[key][1]
            with self.assertRaises(ValueError):verify_binary_minor(o.supports,o.columns,bad)
        bad=copy.deepcopy(o.certificate);bad['keep'][0]=[-1,0,1]
        with self.assertRaises(ValueError):verify_binary_minor(o.supports,o.columns,bad)
        with self.assertRaises(ValueError):
            verify_binary_minor([(0,1)], [0], {'contract':[], 'keep':[[0,0,1]]})
        with self.assertRaises(ValueError):
            verify_binary_minor([(0,1,2)]*2,[1,1], {'contract':[], 'keep':[[0,0,1],[1,0,1]]})
        for columns in ([True],[-2],'011',None):
            with self.assertRaises(ValueError):build_binary_minor(columns)
