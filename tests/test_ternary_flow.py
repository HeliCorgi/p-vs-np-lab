from collections import Counter
from itertools import combinations, product
import unittest

from pnp_lab.modular_hull import modular_hull_refute,check_modular_hull
from pnp_lab.ternary_flow import (onehot_flow,prism_edges,prism_flow,divergence,scramble,
                                  mixed_port_flow,mixed_half_witness,mixed_port_witness)


def holds(cs,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row) for row in cs)


class TernaryFlowTests(unittest.TestCase):
    def test_all_boolean_words_not_just_legal_onehots(self):
        es=((0,1),(1,0),(0,1))  # Tiny parallel-edge truth-table oracle, not the large simple graph.
        for p in (2,3):
            for charge in product(range(p),repeat=2):
                n,cs=onehot_flow(es,charge,p)
                good=set()
                for t in product(range(p),repeat=3):
                    if tuple(((t[0]-t[1]+t[2])*a)%p for a in (1,-1))!=charge:continue
                    if p==2:x=sum(bit<<i for i,bit in enumerate(t))
                    else:x=sum(1<<(3*i+value) for i,value in enumerate(t))
                    good.add(x)
                self.assertEqual({x for x in range(1<<n) if holds(cs,x)},good)

    def test_distribution_after_two_pins(self):
        # K4, oriented low-to-high. Independently enumerate the original trit space.
        es=tuple(combinations(range(4),2))
        for p in (2,3):
            target=(1,p-1,0,0)
            models=[t for t in product(range(p),repeat=6) if divergence(es,t,4,p)==target]
            self.assertEqual(len(models),p**3)
            for a,b in combinations(range(6),2):
                self.assertEqual(Counter((t[a],t[b]) for t in models),
                                 Counter({u:p for u in product(range(p),repeat=2)}))

    def test_signed_encoded_twins_and_wrong_characteristic(self):
        for p in (2,3):
            for bad in (False,True):
                n,cs,x=prism_flow(5,bad,modulus=p)
                cs,x=scramble(n,cs,x,714)
                if not bad:self.assertTrue(holds(cs,x))
                for learn in (2,3):
                    r=modular_hull_refute(n,cs,prime=learn)
                    self.assertEqual(r['status'],'UNSAT' if bad and p==learn else 'UNKNOWN')
                    if r['status']=='UNSAT':self.assertTrue(check_modular_hull(n,cs,r['certificate']))
        self.assertEqual(len(prism_edges(11)),33)

    def test_shared_ports_full_projection_and_lift(self):
        for rhs2,rhs3 in product(range(2),range(3)):
            n,cs,ports,meta=mixed_port_flow(3,binary_rhs=rhs2,ternary_rhs=rhs3)
            self.assertEqual(ports,(1,2,3))
            for bits in product(range(2),repeat=3):
                for p,r,key in ((2,rhs2,'binary'),(3,rhs3,'ternary')):
                    w=mixed_half_witness(3,bits,prime=p,rhs=r)
                    self.assertEqual(w is not None,sum(bits)%p==r)
                    if w is not None:self.assertTrue(holds(meta[key],w))
                both=mixed_port_witness(3,bits,binary_rhs=rhs2,ternary_rhs=rhs3)
                self.assertEqual(both is not None,sum(bits)%2==rhs2 and sum(bits)%3==rhs3)
                if both is not None:self.assertTrue(holds(cs,both))

