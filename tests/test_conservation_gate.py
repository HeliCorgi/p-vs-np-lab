import copy
import random
import unittest
from pnp_lab.conservation import solve_conservation,check_conservation
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.modular_padding import private_chain
from pnp_lab.ternary_flow import prism_flow,scramble,mixed_port_flow
from pnp_lab.four_flow import four_prism_flow
from pnp_lab.mixed_modular import mixed_modular_refute


class GateTests(unittest.TestCase):
    def test_native_results_and_source_binding(self):
        for fixture in (prism_flow,four_prism_flow):
            outputs=[]
            for bad in (True,False):
                n,cs,word=fixture(4,bad=bad);cs,_=scramble(n,cs,word,14414)
                r=solve_pruned(n,cs,max_width=0,conservation=True)
                self.assertEqual((r['status'],r['nodes']),('UNSAT' if bad else 'SAT',0))
                q=r['root_conservation'];self.assertTrue(check_conservation(n,cs,q));outputs.append((cs,q))
            self.assertFalse(check_conservation(n,outputs[1][0],outputs[0][1]))
            word=copy.deepcopy(outputs[1][1]);word['witness']=-1
            self.assertFalse(check_conservation(n,outputs[1][0],word))

    def test_hidden_original_witness_and_tampered_resolution(self):
        for bad in (True,False):
            n,cs,_=prism_flow(3,bad=bad);m,f=private_chain(n,cs,length=3)
            f,_=scramble(m,f,None,14555);r=solve_conservation(m,f)
            self.assertTrue(check_conservation(m,f,r))
            if bad:
                self.assertEqual(r['status'],'UNSAT');c=copy.deepcopy(r)
                self.assertEqual(c['certificate']['kind'],'conservation-resolution-v1')
                c['certificate']['steps'][0][2]=c['certificate']['steps'][0][1]
                self.assertFalse(check_conservation(m,f,c))
            else:self.assertEqual(r['status'],'SAT')

    def test_mixed_budget_and_fallback(self):
        n,cs,*_=mixed_port_flow(4)
        q=solve_conservation(n,cs)
        self.assertEqual((q['status'],q['method']),('UNSAT','mixed'))
        capped=mixed_modular_refute(n,cs,max_probes=0)
        self.assertEqual(capped['status'],'UNKNOWN');self.assertTrue(capped['stats']['budget_limited'])
        self.assertFalse(check_conservation(n,cs,capped))
        rng=random.Random(14139)
        for _ in range(45):
            n=rng.randint(1,5)
            f=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randint(1,3))) for _ in range(rng.randrange(20))]
            sat=any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f) for x in range(1<<n))
            self.assertEqual(solve_pruned(n,f,conservation=True,max_width=None)['status'],'SAT' if sat else 'UNSAT')
