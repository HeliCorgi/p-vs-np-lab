from copy import deepcopy
from itertools import product
import json
import random
import unittest

from pnp_lab.simple_support import GADGET,forcing_models,simple_support_image
from pnp_lab.private_resolution import private_parity_refute
from pnp_lab.split_parity import split_parity_refute,check_split_parity
from pnp_lab.transport_obstruction import switch_tseitin
from pnp_lab.decision_pruning import solve_pruned


def sat(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)


class SplitParityTests(unittest.TestCase):
    def test_root_gate_replays_raw_ids_and_rejects_edited_proofs(self):
        n,cs=switch_tseitin(4)
        cs=tuple(reversed(cs))
        out=solve_pruned(n,cs,max_width=0,split_parity=True)
        self.assertEqual((out['status'],out['nodes']),('UNSAT',0))
        cert=json.loads(json.dumps(out['root_split_parity']['certificate']))
        self.assertTrue(check_split_parity(n,cs,cert))
        self.assertFalse(check_split_parity(n,cs,dict(cert,terms=cert['terms'][1:])))
        bad=deepcopy(cert); q=next(t for t in bad['terms'] if t['pivot'])
        q['one'][0][0]^=1
        self.assertFalse(check_split_parity(n,cs,bad))
        bad=deepcopy(cert);q=next(t for t in bad['terms'] if t['pivot'])
        q['zero'][0][1]=[]
        self.assertFalse(check_split_parity(n,cs,bad))
        self.assertEqual(split_parity_refute(*switch_tseitin(4,odd=False))['status'],'UNKNOWN')

    def test_seeded_oracle_and_empty_clauses(self):
        rng=random.Random(12818)
        for _ in range(260):
            n=rng.randrange(1,7)
            cs=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randint(1,3)))
                for _ in range(rng.randrange(1,27))]
            r=split_parity_refute(n,cs)
            if r['status']=='UNSAT':
                self.assertFalse(any(sat(cs,x) for x in range(1<<n)))
                self.assertTrue(check_split_parity(n,cs,r['certificate']))
        self.assertEqual(split_parity_refute(0,[()])['status'],'UNSAT')
        self.assertEqual(split_parity_refute(0,[])['status'],'UNKNOWN')

    def test_forcing_table_and_blind_class(self):
        self.assertFalse(any(sat(GADGET,x) for x in range(64)))
        ms=forcing_models()
        self.assertTrue(ms)
        self.assertTrue(all((x&56)==56 for x in ms))
        examples=[[(1,2),(-2,)],[(1,2),(-1,-2)],[(1,1,-1),(-1,-1)],[(1,),(-1,)],[],[(),()]]
        for src in examples:
            n,cs,wires=simple_support_image(2,src)
            self.assertEqual(len({frozenset(map(abs,c)) for c in cs}),len(cs))
            self.assertTrue(all(len(set(map(abs,c)))==3 for c in cs))
            images={tuple(bool(x>>(v[0]-1)&1) if v else None for v in wires) for x in range(1<<n) if sat(cs,x)}
            expected={tuple(bool(x>>i&1) if vs else None for i,vs in enumerate(wires)) for x in range(4) if sat(src,x)}
            self.assertEqual(images,expected)
            private=private_parity_refute(n,cs)
            self.assertEqual((private['status'],private['stats']['resolvents_added']),('UNKNOWN',0))
            r=split_parity_refute(n,cs)
            self.assertEqual((r['status'],r['stats']['common_rows'],r['stats']['base_rows']),('UNKNOWN',0,0))

    def test_conserved_rows_survive_renamed_pivots_and_complemented_inputs(self):
        n,cs=switch_tseitin(2)
        ren=[(-1 if i%3==0 else 1)*(n-i) for i in range(n)]
        ds=tuple(tuple(ren[abs(l)-1]*(1 if l>0 else -1) for l in c) for c in reversed(cs))
        q=split_parity_refute(n,ds)
        self.assertEqual(q['status'],'UNSAT')
        self.assertTrue(check_split_parity(n,ds,q['certificate']))
