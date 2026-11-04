import json
import unittest
from itertools import combinations, product

from pnp_lab.trit_solver import check_trit_answer, solve_trit_affine
from pnp_lab.ternary_flow import prism_flow,scramble


def _blocks(n):
    cs=[]
    for t in range(n):
        vs=tuple(3*t+i for i in (1,2,3));cs.append(vs);cs.extend((-x,-y) for x,y in combinations(vs,2))
    return cs


class TritSolverTests(unittest.TestCase):
    def test_classifies_all_512_individual_binary_relations(self):
        words=list(product(range(3),repeat=2))
        for mask in range(512):
            relation={w for i,w in enumerate(words) if mask>>i&1}
            # x-y+z closure characterizes a nonempty affine set; distinct
            # computation from the solver's rank/cardinality check.
            affine=all(tuple((a[i]-b[i]+c[i])%3 for i in range(2)) in relation
                       for a,b,c in product(relation,repeat=3))
            clauses=_blocks(2)+[(-a-1,-b-4) for a,b in words if (a,b) not in relation]
            r=solve_trit_affine(6,clauses)
            want='UNSAT' if not relation else 'SAT' if affine else 'UNKNOWN'
            self.assertEqual(r['status'],want,(mask,relation))
            if want!='UNKNOWN':self.assertTrue(check_trit_answer(6,clauses,r))
            if want=='SAT':
                decoded=[(r['witness']>>(3*i)&7).bit_length()-1 for i in range(2)]
                self.assertIn(tuple(decoded),relation)

    def test_balanced_witness_and_unbalanced_proof_after_scramble(self):
        for odd in (False,True):
            n,cs,_=prism_flow(8,bad=odd)
            cs,_=scramble(n,cs,None,3188);r=solve_trit_affine(n,cs)
            self.assertEqual(r['status'],'UNSAT' if odd else 'SAT')
            self.assertTrue(check_trit_answer(n,cs,json.loads(json.dumps(r))))
            if odd:
                bad=dict(r,certificate=dict(r['certificate'],terms=r['certificate']['terms'][:-1]))
            else:
                # Flipping one indicator breaks exactly-one.
                bad=dict(r,witness=r['witness']^1)
            self.assertFalse(check_trit_answer(n,cs,bad))

    def test_strict_recognition_and_empty_cases(self):
        self.assertEqual(solve_trit_affine(5,[(1,-1)])['status'],'SAT')
        self.assertEqual(solve_trit_affine(0,[()])['status'],'UNSAT')
        self.assertEqual(solve_trit_affine(4,[(1,2,3)])['status'],'UNKNOWN')
        f=_blocks(1)+[(3,4,5),(-3,-4),(-4,-5),(-3,-5)]
        self.assertEqual(solve_trit_affine(5,f)['status'],'UNKNOWN')
        constrained=_blocks(1)+[(1,1),(-2,2)]
        r=solve_trit_affine(7,constrained)
        self.assertEqual((r['status'],r['witness']),('SAT',1))
        # Even while class recognition succeeds a random bit word on these same
        # named coordinates is not certified as SAT.
        self.assertFalse(check_trit_answer(7,constrained,dict(r,witness=2)))
