from itertools import product
import unittest
from pnp_lab.four_flow import four_flow, four_state_word, state_permutations, four_prism_flow, parity_lift
from pnp_lab.ternary_flow import prism_edges, divergence, scramble


def holds(f,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in f)


class FourFlowTests(unittest.TestCase):
    def test_domain_helper_and_all_two_edge_raw_words(self):
        for seeds in (11,59):
            ed=((0,1),(1,0))
            for charge in product(range(4),repeat=2):
                n,cs=four_flow(ed,charge,state_seed=seeds)
                got={x for x in range(1<<n) if holds(cs,x)}
                wanted={four_state_word((a,b),state_seed=seeds) for a,b in product(range(4),repeat=2)
                        if ((a-b)%4,(b-a)%4)==charge}
                self.assertEqual(got,wanted)

    def test_lifting_mod_two_cosets(self):
        # Six edges allows exhaustive parity lifts/classification without solver assumptions.
        ed=((0,1),(0,2),(0,3),(1,2),(1,3),(2,3))
        good=(3,2,3,0);bad=(1,2,3,0)
        models=0
        for word in product((0,1),repeat=6):
            y=parity_lift(ed,good,word)
            self.assertEqual(y is not None,tuple(g%2 for g in good)==divergence(ed,word,4,2))
            self.assertIsNone(parity_lift(ed,bad,word))
            if y is not None:
                self.assertEqual(divergence(ed,y,4,4),good)
                self.assertEqual(tuple(t%2 for t in y),word);models+=1
        self.assertEqual(models,8)

    def test_flow_charges_and_gauge_scramble(self):
        n,g,x=four_prism_flow(3)
        n,b,_=four_prism_flow(3,True)
        g,y=scramble(n,g,x,451);b,z=scramble(n,b,x,451)
        self.assertTrue(holds(g,y));self.assertEqual(y,z);self.assertFalse(holds(b,z))
        self.assertGreater(len(set(state_permutations(len(prism_edges(3)),14144))),1)
