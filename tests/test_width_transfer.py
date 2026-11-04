from itertools import combinations
import json
import unittest

from pnp_lab.width_transfer import cubic_tseitin,guarded,restrict,replay,pull,retract_proof,easy_refutation,closure_small


def holds(cs,word):
    return all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)


class WidthTransferTests(unittest.TestCase):
    def test_truth_strengthening_aliasing_constants_and_flips(self):
        # Image of first axiom is a tautology; its two literals alias with
        # opposite sign. The nontrue child must reuse its OTHER parent.
        h=((1,),(-1,))
        f=((2,-3),(-2,), (3,4),(-4,))
        sig=(1,1,1,False)
        old=[('a',0),('a',1),('r',0,1,2),('a',2),('a',3),('r',3,4,4),('r',5,2,3)]
        self.assertEqual(replay(f,old)[-1],frozenset())
        for s,mapped in [(sig,h),((-1,-1,-1,False),h)]:
            pi=retract_proof(mapped,f,s,old)
            self.assertEqual(replay(mapped,pi)[-1],frozenset())
            self.assertLessEqual(len(pi),len(old))
        self.assertEqual(pull((-3,2),sig),None)
        simple=[('a',0),('w',0,(1,2)),('a',1),('r',1,2,1)]
        po=retract_proof(((1,),(-1,)),((1,),(-1,)),(1,False),simple)
        self.assertEqual(replay(h,po)[-1],frozenset())
        with self.assertRaises(ValueError):replay(h,[('r',0,0,1)])

    def test_entailment_on_sat_source_and_raw_sibling_proofs(self):
        for n,cs,_ in [(1,((1,),(-1,)),True),(2,((1,2),(-1,-2)),False),
                        (3,((1,2,3),(-1,-2,-3)),False)]:
            H=set(map(frozenset,cs))
            for both in (False,True):
                r=guarded(n,cs,contradict_on_true=both)
                m,f,s=r['n'],r['cnf'],r['gate']
                self.assertGreater(m,n)
                self.assertEqual(len({tuple(sorted(map(abs,c))) for c in f}),len(f))
                a=restrict(f,s,False)
                self.assertEqual(set(y for c in a if (y:=pull(c,r['images'])) is not None),H)
                if both:
                    b=restrict(f,s,True);pi=easy_refutation(b);p=replay(b,pi)
                    self.assertFalse(p[-1]);self.assertLessEqual(max(map(len,p)),6)
                else:self.assertTrue(holds(f,r['model']))
        r=guarded(1,((1,),(-1,)),contradict_on_true=True)
        a=restrict(r['cnf'],r['gate'],False)
        p=easy_refutation(a)
        q=retract_proof(((1,),(-1,)),a,r['images'],p)
        self.assertFalse(replay(((1,),(-1,)),json.loads(json.dumps(q)))[-1])

    def test_independent_width_controls(self):
        edges=list(combinations(range(4),2));n,h=cubic_tseitin(4,edges)
        self.assertFalse(any(holds(h,x) for x in range(1<<n)))
        self.assertTrue(holds(cubic_tseitin(4,edges,False)[1],0))
        low=closure_small(h,3);high=closure_small(h,4)
        self.assertFalse(low['contradiction']);self.assertTrue(high['contradiction'])
        rows=replay(h,high['proof']);self.assertFalse(rows[-1]);self.assertEqual(max(map(len,rows)),4)
