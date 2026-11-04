import unittest
from pnp_lab.port_antichain import port_formula,matching_instance,representative_proof
from pnp_lab.width_transfer import cubic_tseitin,pull,replay


def petersen_and_prism():
    def cyc(v,s):return tuple(sorted((v,(v+s)%5)))
    outer=set(cyc(i,1) for i in range(5))
    spokes={(i,i+5) for i in range(5)}
    return [sorted(outer|spokes|{tuple(a+5 for a in cyc(i,s)) for i in range(5)}) for s in (2,1)]


class PortAntichainTests(unittest.TestCase):
    def test_two_same_input_tag_words_and_retractions(self):
        n,t,cnf=port_formula(10);words=[]
        self.assertEqual((n,t,len(cnf)),(465,435,910))
        for edges in petersen_and_prism():
            r=matching_instance(10,edges);words.append(r['tagmask'])
            self.assertEqual(r['tagmask'].bit_count(),15)
            independent=[]
            for clause in cnf:
                tag_lits=[l for l in clause if abs(l)<=t]
                if any((r['tagmask']>>(abs(l)-1)&1)==int(l>0) for l in tag_lits):continue
                independent.append(tuple(l for l in clause if abs(l)>t))
            self.assertEqual(tuple(independent),r['residual'])
            self.assertEqual(len(independent),70)
            _,naked=cubic_tseitin(10,edges)
            images={p for c in independent if (p:=pull(c,r['pull'])) is not None}
            self.assertEqual(images,{frozenset(c) for c in naked})
            pi,lines=representative_proof(r);rows=replay(independent,pi)
            self.assertLessEqual(max(map(len,rows)),3)
            self.assertEqual({rows[i] for i in lines},
                             {frozenset((1 if l>0 else -1)*r['reps'][abs(l)-1] for l in c) for c in naked})
        self.assertNotEqual(*words)

    def test_controls_are_nonisomorphic_and_free_word_is_sat(self):
        short=[]
        for es in petersen_and_prism():
            ns=[set() for _ in range(10)]
            for u,v in es:ns[u].add(v);ns[v].add(u)
            short.append(any(len(ns[u]&ns[v])>=2 for u in range(10) for v in range(u)))
            self.assertTrue(all(sum(bool(mask>>u&1)!=bool(mask>>v&1) for u,v in es)>=4
                                for mask in range(1<<10) if 2<=mask.bit_count()<=8))
        self.assertEqual(short,[False,True])
        n,t,cs=port_formula(10)
        self.assertTrue(all(any(bool((1<<t)>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs))
