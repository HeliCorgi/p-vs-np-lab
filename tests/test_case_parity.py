from copy import deepcopy
import json
import random
import unittest
from pnp_lab.case_parity import case_parity_refute,check_case_parity
from pnp_lab.expander_controls import gated_cubic_siblings


class CaseParityTests(unittest.TestCase):
    def test_two_sides_on_shared_edge_controls_and_tamper(self):
        n,cs,s,_,_=gated_cubic_siblings()
        r=case_parity_refute(n,cs,max_pivots=1)
        self.assertEqual((r['status'],r['stats']['successful_pivot'],r['stats']['inner_calls']),('UNSAT',s,3))
        cert=json.loads(json.dumps(r['certificate']))
        self.assertTrue(check_case_parity(n,cs,cert))
        for bad in (dict(cert,pivot=True),dict(cert,pivot=1),dict(cert,zero=cert['one']),dict(cert,one=None)):
            self.assertFalse(check_case_parity(n,cs,bad))
        bad=deepcopy(cert);bad['one']['parity']['terms']=[]
        self.assertFalse(check_case_parity(n,cs,bad))
        _,even,*_=gated_cubic_siblings(False)
        self.assertFalse(check_case_parity(n,even,cert))
        self.assertEqual(case_parity_refute(n,even,max_pivots=1)['status'],'UNKNOWN')

    def test_budget_constants_and_input_order(self):
        r=case_parity_refute(0,[()],max_pivots=0)
        self.assertTrue(check_case_parity(0,[()],r['certificate']))
        self.assertEqual(r['certificate']['mode'],'root')
        self.assertEqual(case_parity_refute(0,[])['status'],'UNKNOWN')
        n,cs,_,_,_=gated_cubic_siblings();cs=list(reversed(cs))
        r=case_parity_refute(n,cs,max_pivots=0)
        self.assertEqual((r['status'],r['stats']['inner_calls'],r['stats']['pivots_tried']),('UNKNOWN',1,0))
        q=case_parity_refute(n,cs,max_pivots=1,try_root=False)
        self.assertEqual(q['stats']['inner_calls'],2)
        self.assertTrue(check_case_parity(n,cs,q['certificate']))
        for kw in ({'max_pivots':False},{'max_pivots':-1},{'try_root':1}):
            with self.assertRaises(ValueError):case_parity_refute(1,[],**kw)

    def test_small_raw_truth_oracle(self):
        rng=random.Random(13719)
        for _ in range(120):
            n=rng.randrange(1,6)
            cs=[[rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))]
                for _ in range(rng.randrange(1,16))]
            q=case_parity_refute(n,cs)
            if q['status']=='UNSAT':
                self.assertTrue(check_case_parity(n,cs,q['certificate']))
                self.assertFalse(any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) for x in range(1<<n)))
