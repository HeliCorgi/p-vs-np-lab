from itertools import product
import random
import unittest
from pnp_lab.transport_obstruction import (switch_tseitin,restrict,decode_word,critical_model,
                                         conservation_refutation,verify_conservation)


def violated(cs,x):
    return [i for i,c in enumerate(cs) if not any(bool(x&1<<(abs(l)-1))==(l>0) for l in c)]


class TransportObstructionTests(unittest.TestCase):
    def test_decode_blind_to_signed_permutations_and_clause_order(self):
        rng=random.Random(311817)
        for k in (1,2,3,5):
            n,cs=switch_tseitin(k)
            for w in range(1<<k):
                perm=list(range(1,n+1));rng.shuffle(perm)
                p=[v*rng.choice((-1,1)) for v in perm]
                raw=[list(reversed([p[abs(l)-1]*(1 if l>0 else -1) for l in c])) for c in restrict(cs,k,w)]
                rng.shuffle(raw)
                self.assertEqual(decode_word(raw),w)

    def test_clause_deletion_certificates_on_unspecialized_and_partial_instances(self):
        n,cs=switch_tseitin(2)
        for d,w in ((0,0),(1,0),(1,1),(2,1)):
            raw=restrict(cs,d,w)
            for j in range(len(raw)):
                # Exponential assignment search is unnecessary: the model is checked against each raw clause.
                self.assertEqual(violated(raw,critical_model(n,raw,2,j)),[j])

    def test_conservation_proof_from_raw_cnf_and_even_charge_control(self):
        n,cs=switch_tseitin(3)
        proof=conservation_refutation(n,cs)
        self.assertTrue(verify_conservation(n,cs,proof))
        self.assertFalse(verify_conservation(n,cs,proof[1:]))
        for d,w in ((2,0),(2,3),(3,5)):
            rows=restrict(cs,d,w)
            self.assertTrue(verify_conservation(n,rows,conservation_refutation(n,rows)))
        _,even=switch_tseitin(3,odd=False)
        self.assertEqual(violated(even,0),[])
        self.assertFalse(verify_conservation(n,even,proof))
        self.assertIsNone(conservation_refutation(n,even))

    def test_semantic_replay_for_small_mutated_families(self):
        # Accepted proofs must refute the *raw* signed formula. Include branch-conditioned
        # equalities, duplicate literals in a submitted bogus proof and missing premises.
        eqs=[(1,-2,3),(1,2,-3),(-1,-2,3),(-1,2,-3)]
        neq=[(2,3),(-2,-3)]
        proof=[('guard',1,((2,3),),((2,3),)),('star',(2,3),1)]
        for keep in product((False,True),repeat=6):
            rows=[c for c,b in zip(eqs+neq,keep) if b]
            accepted=verify_conservation(3,rows,proof)
            actual=not any(not violated(rows,x) for x in range(8))
            self.assertEqual(accepted,actual)
        self.assertFalse(verify_conservation(3,eqs+neq,[('star',(2,2),1)]))


if __name__=='__main__':unittest.main()
