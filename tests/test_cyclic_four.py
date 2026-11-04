import copy
from itertools import combinations,product
import json
import random
import unittest

from pnp_lab.cyclic_four import _solve,check_cyclic_four,solve_cyclic_four
from pnp_lab.four_flow import four_prism_flow
from pnp_lab.ternary_flow import scramble


def domain(i):
    u,v,w,z,h=range(5*i+1,5*i+6)
    return [(u,v,h),(-h,w,z)]+[(-a,-b) for a,b in combinations((u,v,w,z),2)]


def constraints(group,ok):
    return [tuple(-(5*i+c+1) for i,c in zip(group,state))
            for state in product(range(4),repeat=len(group)) if not ok(*state)]


class CyclicFourTests(unittest.TestCase):
    def test_torsion_not_field_elimination(self):
        rng=random.Random(14404)
        for i in range(250):
            n=rng.randint(1,3)
            f=[({j:a for j in range(n) if (a:=rng.choice((0,2) if i%2 else range(4)))},
                rng.randrange(4)) for _ in range(rng.randrange(1,6))]
            models=[x for x in product(range(4),repeat=n) if all(sum(a*x[v] for v,a in r.items())%4==b for r,b in f)]
            word,p,_,_=_solve(f,n)
            if models:
                self.assertIn(tuple(word),models);self.assertIsNone(p)
            else:
                self.assertIsNone(word)
                self.assertTrue(all(sum(c*f[j][0].get(v,0) for j,c in p.items())%4==0 for v in range(n)))
                self.assertNotEqual(sum(c*f[j][1] for j,c in p.items())%4,0)
        self.assertEqual(_solve([({0:2},1)],1)[1],{0:2})
        self.assertEqual(_solve([({0:2},2)],1)[0],[1])

    def test_hidden_flows_and_independent_raw_checker(self):
        for seed in (1,2,17,45051):
            for bad in (False,True):
                n,f,_=four_prism_flow(3,bad=bad,state_seed=seed)
                f,_=scramble(n,f,None,77*seed)
                r=solve_cyclic_four(n,f)
                self.assertEqual(r['status'],'UNSAT' if bad else 'SAT')
                self.assertTrue(check_cyclic_four(n,f,json.loads(json.dumps(r))))
                alt=copy.deepcopy(r)
                if bad:
                    self.assertEqual(r['stats']['residual_rhs'],2)
                    alt['certificate']['terms'][0]['rhs']^=1
                else:
                    # Flip an indicator (not just an unused variable).
                    alt['witness']^=1
                self.assertFalse(check_cyclic_four(n,f,alt))

    def test_incompatible_coordinates_and_nongroup_law(self):
        f=[c for i in range(5) for c in domain(i)]
        s=(0,2,1,3)
        f+=constraints((0,1,2),lambda a,b,c:(a+b+c)%4==0)
        f+=constraints((0,3,4),lambda a,b,c:(s[a]+b+c)%4==0)
        got=solve_cyclic_four(25,f)
        self.assertEqual((got['status'],got['reason']),('UNKNOWN','incompatible local state calibrations'))
        other=[c for i in range(3) for c in domain(i)]+constraints((0,1,2),lambda a,b,c:a^b^c==0)
        self.assertEqual(solve_cyclic_four(15,other)['status'],'UNKNOWN')
        self.assertEqual(solve_cyclic_four(0,[])['status'],'SAT')
        self.assertTrue(check_cyclic_four(0,[()],solve_cyclic_four(0,[()])))
