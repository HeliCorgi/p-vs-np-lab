from itertools import product
import unittest
from pnp_lab.transport_obstruction import critical_model, restrict, switch_tseitin
from pnp_lab.transport_resolution_padding import contract_twice, padded_tseitin
from pnp_lab.split_parity import split_parity_refute
from pnp_lab.private_resolution import private_parity_refute,check_private_parity


def truth(c,x):
    return any(bool(x&(1<<(abs(l)-1)))==(l>0) for l in c)


class TransportPaddingTests(unittest.TestCase):
    def test_critical_model_for_every_padded_root_clause(self):
        k=1;base,src=switch_tseitin(k);_,dst=padded_tseitin(k)
        helpers={};index=base;owner=[]
        for i,c in enumerate(src):
            if min(map(abs,c))<=k:owner.append((i,None))
            else:
                index+=1;helpers[i]=index
                owner.extend(((i,0),(i,1)))
        self.assertEqual(len(dst),len(owner))
        for j,(i,side) in enumerate(owner):
            model=critical_model(base,src,k,i)
            for t,w in helpers.items():
                # In the bad original clause both halves' old literals are false.
                bit=(side==1) if t==i else not truth(src[t][:-1],model)
                if bit:model |= 1<<(w-1)
            self.assertEqual([q for q,c in enumerate(dst) if not truth(c,model)],[j])

    def test_contraction_named_scope_at_many_prefixes(self):
        k=3;_,old=switch_tseitin(k);n,new=padded_tseitin(k)
        for d in range(k+1):
            for word in range(1<<d):
                self.assertEqual(contract_twice(restrict(new,d,word)),
                                 frozenset(map(frozenset,restrict(old,d,word))))

    def test_odd_even_raw_gate_and_resolved_proof(self):
        for odd in (False,True):
            n,cs=padded_tseitin(2,odd=odd)
            self.assertEqual(split_parity_refute(n,cs)['status'],'UNKNOWN')
            ans=private_parity_refute(n,cs)
            if odd:self.assertTrue(check_private_parity(n,cs,ans['certificate']))
            else:
                self.assertEqual(ans['status'],'UNKNOWN')
                # All-zero original variables satisfy the even sibling; extend each helper.
                n0,orig=switch_tseitin(2,odd=False);w=n0;x=0
                for c in orig:
                    if min(map(abs,c))<=2:continue
                    w+=1
                    if not truth(c[:-1],x):x|=1<<(w-1)
                self.assertTrue(all(truth(c,x) for c in cs))

if __name__=='__main__':unittest.main()
