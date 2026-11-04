import copy
import json
from itertools import combinations
import random
import unittest

from pnp_lab.private_resolution import private_parity_refute,check_private_parity
from pnp_lab.split_parity import split_parity_refute


def holds(c,w):
    return any(bool(w>> (abs(l)-1)&1)==(l>0) for l in c)


def fixture(charge):
    edges=list(combinations(range(4),2));n=len(edges)
    original=[];padded=[]
    for v in range(4):
        variables=[i+1 for i,e in enumerate(edges) if v in e]
        for w in range(8):
            if w.bit_count()%2==charge>>v&1:continue
            c=tuple(-j if w>>i&1 else j for i,j in enumerate(variables))
            n+=1;original.append(c)
            padded.extend([(c[0],n),(-n,c[1],c[2])])
    return n,original,padded


class PrivateResolutionTests(unittest.TestCase):
    def test_tetrahedron_all_charges_with_constructed_raw_sat_witnesses(self):
        for charge in range(16):
            n,base,cs=fixture(charge)
            candidates=[x for x in range(64) if all(holds(c,x) for c in base)]
            self.assertEqual(bool(candidates),charge.bit_count()%2==0)
            self.assertEqual(split_parity_refute(n,cs)['status'],'UNKNOWN')
            r=private_parity_refute(n,cs)
            self.assertEqual(r['stats']['resolvents_added'],16)
            if candidates:
                x=candidates[0]
                # If the original first literal does not hold, set the gate;
                # the remaining two literals must then contain a true one.
                for j,c in enumerate(base):
                    if not holds(c[:1],x):x|=1<<(6+j)
                self.assertTrue(all(holds(c,x) for c in cs))
                self.assertEqual((r['status'],r['certificate']),('UNKNOWN',None))
            else:
                self.assertEqual(r['status'],'UNSAT')
                cert=json.loads(json.dumps(r['certificate']))
                self.assertTrue(check_private_parity(n,cs,cert))
                self.assertEqual([row['clause'] for row in cert['resolution']],
                                 [list(c) for c in base])

    def test_replay_rejects_fake_steps_and_malformed_nested_certificates(self):
        n,_,cs=fixture(1)
        c=private_parity_refute(n,cs)['certificate']
        for field,val in [('id',len(cs)+1),('pivot',True),('positive_parent',len(cs)),
                          ('negative_parent',0),('pivot',22),('clause',[1]),('clause',[True])]:
            forged=copy.deepcopy(c);forged['resolution'][0][field]=val
            self.assertFalse(check_private_parity(n,cs,forged))
        for c2 in (dict(c,kind='wrong'),dict(c,parity={}),dict(c,resolution=None),
                   dict(c,resolution=c['resolution'][::-1]),dict(c,resolution=[])):
            self.assertFalse(check_private_parity(n,cs,c2))
        # The old certificate cannot be reused with the opposite total charge.
        self.assertFalse(check_private_parity(n,fixture(0)[2],c))

    def test_one_layer_width_and_premise_guards(self):
        # Closing this implication chain transitively would derive (2,5).
        cs=[(1,2),(-1,3),(-3,4),(-4,5),(6,),(-6,)]
        r=private_parity_refute(6,cs);self.assertEqual(r['status'],'UNSAT')
        additions=[z['clause'] for z in r['certificate']['resolution']]
        self.assertCountEqual(additions,[[2,3],[-1,4],[-3,5],[]])
        self.assertFalse([2,5] in additions)
        for raw in ([(1,2,3),(-1,4,5)],[(1,2),(-1,-2)],[(1,1,2),(-1,3)],
                    [(1,2),(-1,3),(2,3)],[(1,-1)]):
            self.assertEqual(private_parity_refute(5,raw)['stats']['resolvents_added'],0)
        with self.assertRaises(ValueError):private_parity_refute(4,[(1,2,3,4)])
        with self.assertRaises(ValueError):private_parity_refute(2,[(True,)])

    def test_random_returned_refutations_against_point_oracle(self):
        rng=random.Random(136205);detected=0
        for _ in range(140):
            n=rng.randint(2,5);cs=[]
            for _ in range(rng.randrange(16)):
                size=rng.randint(1,min(3,n))
                cs.append([v*rng.choice((-1,1)) for v in rng.sample(range(1,n+1),size)])
            r=private_parity_refute(n,cs)
            sat=any(all(holds(c,x) for c in cs) for x in range(1<<n))
            if r['status']=='UNSAT':
                detected+=1;self.assertFalse(sat)
                self.assertTrue(check_private_parity(n,cs,r['certificate']))
            else:self.assertIsNone(r['certificate'])
        self.assertGreater(detected,10)
