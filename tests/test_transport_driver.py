import json
import random
import unittest

from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.witness_transport import check_transport,apply_transport


def sat(c,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in c)


class DirectedDriverTests(unittest.TestCase):
    def test_actual_drops_have_replayable_witness_maps(self):
        # With s=1 the two binary clauses force a=z. With s=0 the
        # disjunction only needs a OR z; flipping z is a sufficient map.
        cs=((1,2,3),(-1,2,-3),(-1,-2,3))
        r=solve_pruned(3,cs,label_mode='syntax',transport=True,transport_strategies=('flip',),
                       transport_trace=True,anchor_collisions=False,max_width=None)
        self.assertEqual(r['status'],'SAT')
        trace=json.loads(json.dumps(r['transport_trace']))
        self.assertGreater(len(trace),0)
        for step in trace:
            a,b,c=step['source'],step['target'],step['certificate']
            self.assertTrue(check_transport(3,a,b,c))
            for model in range(8):
                if sat(a,model):self.assertTrue(sat(b,apply_transport(3,c,model)))
        capped=solve_pruned(3,cs,label_mode='syntax',anchor_collisions=False,transport=True,
                            max_transport_checks=0,max_width=1)
        self.assertEqual((capped['status'],capped['stats']['transport_drops']),('UNKNOWN',0))

    def test_unrestricted_small_source_decisions_with_directional_pruning(self):
        rng=random.Random(381926)
        for _ in range(105):
            n=rng.randrange(1,7)
            f=tuple(tuple(v*rng.choice((-1,1)) for v in rng.sample(range(1,n+1),min(n,rng.randint(1,3))))
                    for _ in range(rng.randint(1,28)))
            sat_expected=any(sat(f,x) for x in range(1<<n))
            r=solve_pruned(n,f,label_mode='syntax',anchor_collisions=bool(rng.randrange(2)),
                           transport=True,split_parity=True,max_width=None)
            self.assertEqual(r['status'],'SAT' if sat_expected else 'UNSAT')
