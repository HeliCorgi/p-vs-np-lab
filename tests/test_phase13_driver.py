import copy
import random
import unittest
from pnp_lab.decision_pruning import solve_pruned
from pnp_lab.interface_transport import find_interface_transport
from pnp_lab.derived_transport import check_derived_transport
from pnp_lab.recovered_parity import check_recovered_parity
from pnp_lab.simple_support import simple_support_image
from pnp_lab.transport_obstruction import switch_tseitin,restrict
from pnp_lab.transport_resolution_padding import padded_tseitin


class PhaseThirteenDriverTests(unittest.TestCase):
    def test_renamed_signed_antichain_and_budgets(self):
        n,cs=padded_tseitin(2)
        a,b=restrict(cs,2,1),restrict(cs,2,2)
        perm=list(range(1,n+1));rng=random.Random(1312);rng.shuffle(perm)
        perm=[v*rng.choice((1,-1)) for v in perm]
        def rename(rows):
            return tuple(tuple(perm[abs(l)-1]*(1 if l>0 else -1) for l in c) for c in reversed(rows))
        a,b=rename(a),rename(b)
        r=find_interface_transport(n,a,b)
        self.assertTrue(check_derived_transport(n,a,b,r['certificate']))
        saved=solve_pruned(n,cs,derived_depth=0,label_mode='syntax',max_width=1,max_transport_checks=2,transport_trace=True)
        self.assertEqual(saved['widths'][:3],[1,1,1])
        for line in saved['transport_trace']:
            self.assertTrue(check_derived_transport(n,line['source'],line['target'],line['certificate']))
        capped=solve_pruned(n,cs,derived_depth=0,label_mode='syntax',max_width=1,max_proof_nodes=0,anchor_collisions=False)
        self.assertEqual((capped['status'],capped['stats']['transport_drops']),('UNKNOWN',0))
        self.assertTrue(capped['stats']['derivation']['budget_limited'])

    def test_original_input_bound_by_composed_checker(self):
        n,src=switch_tseitin(1)
        m,cs,_=simple_support_image(n,src)
        r=solve_pruned(m,cs,recover_parity=True,max_width=0)
        cert=r['root_recovered_parity']['certificate']
        self.assertEqual((r['status'],r['nodes']),('UNSAT',0))
        self.assertTrue(check_recovered_parity(m,cs,cert))
        bad=copy.deepcopy(cert);bad['inner']['terms'].pop()
        self.assertFalse(check_recovered_parity(m,cs,bad))
        _,even=switch_tseitin(1,odd=False)
        _,sat_cs,_=simple_support_image(n,even)
        self.assertFalse(check_recovered_parity(m,sat_cs,cert))

    def test_small_raw_decisions_against_independent_assignments(self):
        rng=random.Random(1312)
        for _ in range(55):
            n=rng.randrange(1,6)
            cs=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randint(1,3)))
                for j in range(rng.randrange(0,22))]
            sat=any(all(any(bool((x>>(abs(l)-1))&1)==(l>0) for l in c) for c in cs) for x in range(1<<n))
            r=solve_pruned(n,cs,derived_depth=rng.randrange(2),transport=bool(rng.randrange(2)),
                           max_proof_nodes=12,label_mode='syntax',max_width=None)
            self.assertEqual(r['status'],'SAT' if sat else 'UNSAT')
