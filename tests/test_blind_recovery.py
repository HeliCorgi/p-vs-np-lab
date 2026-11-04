import json
from copy import deepcopy
import random
import unittest
from pnp_lab.blind_recovery import recover_blind,check_recovery,lift_recovered_model
from pnp_lab.simple_support import simple_support_image
from pnp_lab.transport_obstruction import switch_tseitin
from pnp_lab.split_parity import split_parity_refute,check_split_parity


def sat(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)


class BlindRecoveryTests(unittest.TestCase):
    def test_arbitrary_raw_inputs_exhaustive_on_model_transfer(self):
        rng=random.Random(17013)
        for _ in range(140):
            n=rng.randrange(0,8)
            lengths=rng.randrange(0,2*n+3)
            rows=[tuple(rng.choice((-1,1))*v for v in rng.sample(range(1,n+1),min(n,rng.randint(1,3)))) for _ in range(lengths)]
            original=[x for x in range(1<<n) if sat(rows,x)]
            r=recover_blind(n,rows);self.assertTrue(check_recovery(n,rows,r))
            reduced=[z for z in range(1<<r['n_reduced']) if sat(r['clauses'],z)]
            self.assertEqual(bool(original),bool(reduced))
            for z in reduced:self.assertIn(lift_recovered_model(n,rows,r,z),original)
            for x in original:
                a={}
                for j,l in enumerate(r['images']):
                    if type(l) is bool:continue
                    b=bool(x>>j&1)==(l>0)
                    self.assertEqual(a.setdefault(abs(l),b),b)
                zz=sum(1<<(v-1) for v,b in a.items() if b)
                self.assertIn(zz,reduced)

    def test_tree_contrapositions_and_forged_result(self):
        n=5;rows=((-1,-2),(2,3),(-3,1),(1,4,5),(-1,-4,-5))
        r=json.loads(json.dumps(recover_blind(n,rows)))
        self.assertTrue(check_recovery(n,rows,r));self.assertGreater(r['stats']['signed_components'],0)
        for field in ('out','back'):
            bad=deepcopy(r);edge=bad['certificate']['groups'][0][field][0];edge[2]=len(rows)-1
            self.assertFalse(check_recovery(n,rows,bad))
        bad=deepcopy(r);idx=next(i for i,x in enumerate(r['images']) if type(x) is int)
        bad['images'][idx]=True;self.assertFalse(check_recovery(n,rows,bad))

    def test_unsat_from_packs_and_binary_cycle(self):
        n,raw,_=simple_support_image(3,[()]);a=recover_blind(n,raw)
        self.assertTrue(check_recovery(n,raw,a));self.assertEqual(a['status'],'UNSAT')
        raw=[(1,2),(-2,1),(-1,3),(-3,-1)]
        a=recover_blind(3,raw);self.assertTrue(check_recovery(3,raw,a));self.assertEqual(a['status'],'UNSAT')
        with self.assertRaises(ValueError):lift_recovered_model(3,raw,a,0)

    def test_nested_certificate_original_order_and_named_checks(self):
        n,src=switch_tseitin(4);nb,raw,_=simple_support_image(n,src)
        raw=list(reversed(raw));r=json.loads(json.dumps(recover_blind(nb,raw)))
        self.assertTrue(check_recovery(nb,raw,r))
        p=split_parity_refute(r['n_reduced'],r['clauses'])
        self.assertTrue(check_split_parity(r['n_reduced'],r['clauses'],p['certificate']))
        bad=deepcopy(r);bad['certificate']['packs'][0]['clauses']=[0]
        self.assertFalse(check_recovery(nb,raw,bad))
        wrong=deepcopy(r);wrong['clauses']=[]
        self.assertFalse(check_recovery(nb,raw,wrong))
