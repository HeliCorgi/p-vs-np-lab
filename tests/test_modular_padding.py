from copy import deepcopy
from itertools import product
import json,random
import unittest
from pnp_lab.modular_padding import (private_chain,plant_chain_model,shield_equalities,peel,lift_after_peeling,
                                     peeled_modular_refute,check_peeled_modular)
from pnp_lab.ternary_flow import prism_flow,scramble
from pnp_lab.modular_hull import modular_hull_refute


def holds(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)


class ModularPaddingTests(unittest.TestCase):
    def test_elimination_equivalence_and_reverse_lifting_raw(self):
        rng=random.Random(140923)
        # Includes taut resolvents, units, empty clauses, and width-four pairs that must be skipped.
        forms=[(3,((1,2),(-1,-2))), (2,((1,),(-1,))), (5,((1,2,3),(-1,4,5))),
               (2,((1,-1),(-2,),(-2,))), (2,((1,2),(-1,2),(2,)))]
        for _ in range(70):
            n=rng.randrange(1,6)
            forms.append((n,tuple(tuple(rng.choice((-1,1))*rng.randint(1,n) for i in range(rng.randrange(1,4)))
                                  for j in range(rng.randrange(12)))))
        for n,cs in forms:
            out,steps=peel(n,cs);res=[x for x in range(1<<n) if holds(out,x)]
            self.assertEqual(bool(res),any(holds(cs,x) for x in range(1<<n)))
            for x in res:
                y=lift_after_peeling(n,cs,steps,x)
                self.assertTrue(holds(cs,y))
                used={v for v,i,j in steps}
                self.assertTrue(all((x^y)>>(v-1)&1==0 for v in range(1,n+1) if v not in used))

    def test_chain_reconstruction_and_refutation_tampering(self):
        n,cs,_=prism_flow(3,True);m,f=private_chain(n,cs,length=3)
        rows,steps=peel(m,f)
        self.assertEqual(set(map(frozenset,rows)),set(map(frozenset,cs)))
        self.assertEqual(len(steps),3*len(cs))
        shuffled,_=scramble(m,f,None,534)
        r=peeled_modular_refute(m,shuffled)
        cert=json.loads(json.dumps(r['certificate']))
        self.assertTrue(check_peeled_modular(m,shuffled,cert))
        bad=deepcopy(cert);bad['steps'][0][1]=bad['steps'][0][2]
        self.assertFalse(check_peeled_modular(m,shuffled,bad))
        bad=deepcopy(cert);bad['inner']['terms']=[]
        self.assertFalse(check_peeled_modular(m,shuffled,bad))
        bad=deepcopy(cert);bad['steps'][1][1]=len(shuffled)+len(steps)+3
        self.assertFalse(check_peeled_modular(m,shuffled,bad))
        n,cs,x=prism_flow(3)
        m,f=private_chain(n,cs,length=3)
        w=plant_chain_model(n,cs,x,length=3);self.assertTrue(holds(f,w))
        # Discovery must work without a known planted value for a single helper.
        self.assertTrue(holds(f,lift_after_peeling(m,f,peel(m,f)[1],x)))

    def test_any_field_local_partial_chain_and_shield(self):
        n,f=private_chain(3,((1,2,3),(-1,-2,-3)),length=10)
        m,shield,_=shield_equalities(n,f)
        for p in (2,3):
            bare=modular_hull_refute(n,f,prime=p)
            self.assertEqual((bare['status'],bare['stats']['local_rows']),('UNKNOWN',0))
            no=peeled_modular_refute(m,shield,prime=p)
            self.assertEqual((no['status'],no['stats']['steps'],no['stats']['modular']['global_rank']),
                             ('UNKNOWN',0,2*n))
