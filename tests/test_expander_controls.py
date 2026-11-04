import unittest
from itertools import combinations
from pnp_lab.expander_controls import NAMES,cubic_control,four_cycles,components,critical_assignment,finite_ceiling,gated_cubic_siblings,sibling_at
from pnp_lab.witness_transport import check_transport,apply_transport
from pnp_lab.derived_transport import derive_transport,check_derived_transport


class RigidCeilingTests(unittest.TestCase):
    def test_odd_defects_and_even_solutions_by_raw_edge_enumeration(self):
        for name in NAMES:
            edges,cs=cubic_control(name)
            self.assertEqual(len(edges),len(set(edges)))
            stars=[sum(1<<i for i,e in enumerate(edges) if v in e) for v in range(10)]
            self.assertTrue(all(m.bit_count()==3 for m in stars))
            syndromes={}
            for x in range(1<<15):
                y=sum(((m&x).bit_count()%2)<<i for i,m in enumerate(stars))
                syndromes[y]=syndromes.get(y,0)+1
            self.assertEqual(syndromes.get(1,0),0)
            self.assertEqual(syndromes[0],64)
            for j,c in enumerate(cs):
                x=critical_assignment(edges,c)
                fail=[i for i,row in enumerate(cs) if not any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row)]
                self.assertEqual(fail,[j])

    def test_cuts_and_unsigned_nonisomorphism(self):
        observed=[]
        for name in NAMES:
            edges,cs=cubic_control(name)
            count=sum(all(sum(v in e and set(e)<=set(q) for e in edges)==2 for v in q)
                      for q in combinations(range(10),4))
            self.assertEqual(count,four_cycles(edges));observed.append(count)
            cutstars={tuple(i for i,e in enumerate(edges,1) if v in e) for v in range(10)}
            self.assertEqual(cutstars,{removed for k in range(4) for removed in combinations(range(1,16),k)
                                       if len(components(edges,removed))>1})
            q=finite_ceiling(name)
            self.assertEqual((q['width_at_most_three_nonraw'],q['width_at_most_three_raw']),(4051,40))
        self.assertEqual(observed,[0,5])

    def test_sibling_retraction_on_raw_even_models_and_odd_clauses(self):
        for odd in (True,False):
            n,cs,s,t,maps=gated_cubic_siblings(odd)
            for side in range(2):
                d=sibling_at(cs,s,side)
                cert=dict(kind='signed-substitution-v1',images=maps[side])
                self.assertTrue(check_transport(n,t[side],d,cert))
                p=derive_transport(n,d,t[side],images=list(range(1,n+1)),depth=0)
                self.assertTrue(check_derived_transport(n,d,t[side],p['certificate']))
                if not odd:
                    word=apply_transport(n,cert,side<<(s-1))
                    self.assertTrue(all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs))
