import copy
import json
import random
import unittest
from itertools import product

from pnp_lab.derived_transport import (apply_derived_transport,check_clause,
    check_derived_transport,derive_clause,derive_transport)
from pnp_lab.simple_support import GADGET
from pnp_lab.witness_transport import check_transport


def holds(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)


class DerivedTransportTests(unittest.TestCase):
    def test_beyond_all_raw_maps_on_minimal_unsat_pair(self):
        target=tuple(product((1,-1),(2,-2)))
        src=[]
        for i,(a,b) in enumerate(target,3):
            src.extend([(a,i),(-i,b)])
        # Each source clause is essential, so four raw target clauses cannot
        # justify all eight; removing any unreferenced input clause gives a model.
        for i in range(len(src)):
            self.assertTrue(any(holds(src[:i]+src[i+1:],w) for w in range(64)))
        self.assertFalse(any(holds(src,w) for w in range(64)))
        out=derive_transport(6,src,target,depth=0)
        c=json.loads(json.dumps(out['certificate']))
        self.assertTrue(check_derived_transport(6,src,target,c))
        self.assertFalse(check_transport(6,src,target,dict(c,kind='signed-substitution-v1')))
        self.assertTrue(all('conflict' in pr and pr['units'] for pr in c['clauses']))
        for field in ('conflict','units'):
            tamper=copy.deepcopy(c);tamper['clauses'][0][field]=999 if field=='conflict' else []
            self.assertFalse(check_derived_transport(6,src,target,tamper))

    def test_flip_discovered_using_consequences_and_actual_witnesses(self):
        src=((1,3),(-3,2),(-1,4),(-4,-2)) # existential split XOR
        target=((1,-2),(-1,2))
        r=derive_transport(4,src,target,strategies=('flip',),depth=0)
        cert=r['certificate']
        self.assertTrue(check_derived_transport(4,src,target,cert))
        self.assertNotEqual(cert['images'],list(range(1,5)))
        self.assertEqual(r['stats']['queries'],4) # all possible signs on one support
        models=[x for x in range(16) if holds(src,x)]
        self.assertTrue(models)
        for x in models:self.assertTrue(holds(target,apply_derived_transport(4,cert,x)))
        bad=copy.deepcopy(cert);bad['images'][1]*=-1
        self.assertFalse(check_derived_transport(4,src,target,bad))
        capped=derive_transport(4,src,target,strategies=('flip',),max_queries=2)
        self.assertEqual((capped['status'],capped['stats']['queries'],capped['stats']['budget_limited']),('UNKNOWN',2,True))

    def test_distinct_support_gadget_lookahead_and_budget(self):
        src=GADGET[1:]
        for v,d in [(4,1),(5,1),(6,2)]:
            self.assertEqual(derive_clause(6,src,(v,),depth=d-1)['status'],'UNKNOWN')
            out=derive_clause(6,src,(v,),depth=d)
            self.assertTrue(check_clause(6,src,(v,),out['proof']))
            q=out['stats']['nodes']
            small=derive_clause(6,src,(v,),depth=d,max_nodes=q-1)
            self.assertEqual((small['status'],small['stats']['nodes'],small['stats']['budget_limited']),
                             ('UNKNOWN',q-1,True))
            self.assertFalse(check_clause(6,src,(-v,),out['proof']))
            bad=copy.deepcopy(out['proof']);bad['zero']=bad['one']
            self.assertFalse(check_clause(6,src,(v,),bad))
        with self.assertRaises(ValueError):derive_clause(6,src,(4,),depth=4)
        with self.assertRaises(ValueError):derive_transport(6,src,[(4,)],max_nodes=True)

    def test_semantic_oracle_for_signed_folds_and_partial_search(self):
        rng=random.Random(113803)
        proved=rejected=0
        for _ in range(210):
            n=4
            def cnf():
                return [tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(4)))
                        for _ in range(rng.randrange(8))]
            a,b=cnf(),cnf()
            images=tuple(rng.choice((False,True,1,2,-2,4,-4)) for _ in range(n))
            out=derive_transport(n,a,b,images=images,depth=2)
            cert=out['certificate']
            if cert is None:
                rejected+=1;continue
            proved+=1
            self.assertTrue(check_derived_transport(n,a,b,cert))
            for x in range(1<<n):
                if holds(a,x):self.assertTrue(holds(b,apply_derived_transport(n,cert,x)))
        self.assertGreater(proved,30);self.assertGreater(rejected,30)

    def test_fixed_depth_is_not_a_complete_implication_oracle(self):
        # All 8 signed triples together are unsatisfiable; with no assumptions
        # unit propagation is silent, as is one binary split.
        f=tuple(product((1,-1),(2,-2),(3,-3)))
        self.assertEqual(derive_clause(3,f,(),depth=1)['status'],'UNKNOWN')
        self.assertEqual(derive_clause(3,f,(),depth=2)['status'],'PROVED')
        self.assertTrue(check_clause(3,[(1,-1)],(2,-2),{'true':True}))
        self.assertFalse(check_clause(3,[(1,2)],(2,),{'true':True}))
        self.assertFalse(check_clause(3,[(1,2)],(),{'units':[], 'conflict':False}))
