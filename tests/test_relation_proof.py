import copy
from itertools import product
import unittest

from pnp_lab.modular_barrier import line_fixture
from pnp_lab.relation_proof import (KIND, check_relation_proof,
                                     resolution_to_relations)
from pnp_lab.resolution_closure import resolution_refute


class RelationProofTests(unittest.TestCase):
    def test_shared_witness_is_required_before_projection(self):
        # Each pair of clauses gives equality or disequality. Both unary
        # projections are full, but their join has no shared Boolean witness.
        cs = [(1, 2), (-1, -2), (1, -2), (-1, 2)]
        nodes = [dict(op='input', clause=i, scope=[1, 2], table=t)
                 for i, t in enumerate((14, 7, 11, 13))]
        nodes += [dict(op='join-project', left=0, right=1, scope=[1, 2], table=6),
                  dict(op='join-project', left=2, right=3, scope=[1, 2], table=9),
                  dict(op='join-project', left=4, right=5, scope=[], table=0)]
        cert = dict(kind=KIND, variables=2, union_width=2, nodes=nodes, root=6)
        self.assertTrue(check_relation_proof(2, cs, cert))
        wrong = copy.deepcopy(cert)
        wrong['nodes'][4]['scope'] = [1]
        wrong['nodes'][4]['table'] = 3
        wrong['nodes'][5]['scope'] = [1]
        wrong['nodes'][5]['table'] = 3
        self.assertFalse(check_relation_proof(2, cs, wrong))

    def test_core_exact_tables_and_hidden_union_budget(self):
        n, cs = line_fixture(0)
        cs = cs[:152]
        resolution = resolution_refute(n, cs, width=4)
        report = resolution_to_relations(n, cs, resolution['certificate'], max_union_width=5)
        self.assertEqual(report['status'], 'UNSAT')
        self.assertTrue(check_relation_proof(n, cs, report['certificate']))
        self.assertEqual(report['stats']['max_relation_width'], 4)
        self.assertEqual(report['stats']['union_width'], 5)
        self.assertEqual(report['stats']['enumerated_cells'], 6398)
        positive = tuple(tuple(map(abs, c)) for c in cs)
        self.assertFalse(check_relation_proof(n, positive, report['certificate']))
        for kwargs in (dict(max_union_width=4), dict(max_nodes=0), dict(max_cells=0)):
            out = resolution_to_relations(n, cs, resolution['certificate'], **kwargs)
            self.assertEqual(out['status'], 'UNKNOWN')
            self.assertTrue(out['stats']['budget_limited'])
            self.assertIsNone(out['certificate'])
            self.assertFalse(check_relation_proof(n, cs, report['certificate'], **kwargs))

    def test_tampering_and_sparse_original_labels(self):
        huge = 10**12
        cs = [(huge,), (-huge,)]
        guide = resolution_refute(huge, cs, width=1)
        cert = resolution_to_relations(huge, cs, guide['certificate'])['certificate']
        self.assertTrue(check_relation_proof(huge, cs, cert))
        loose = copy.deepcopy(guide['certificate'])
        loose['width'] = huge
        self.assertEqual(resolution_to_relations(huge, cs, loose,
                         max_union_width=1)['status'], 'UNSAT')
        for mutation in ('table', 'future', 'scope', 'width', 'bound', 'root', 'bool'):
            bad = copy.deepcopy(cert)
            if mutation == 'table':
                bad['nodes'][0]['table'] ^= 1
            elif mutation == 'future':
                bad['nodes'][-1]['left'] = len(bad['nodes']) - 1
            elif mutation == 'scope':
                bad['nodes'][-1]['scope'] = [huge - 1]
            elif mutation == 'width':
                bad['union_width'] = 0
            elif mutation == 'bound':
                bad['variables'] = huge - 1
            elif mutation == 'root':
                bad['root'] = 0
            else:
                bad['nodes'][0]['clause'] = True
            self.assertFalse(check_relation_proof(huge, cs, bad), mutation)
        empty = dict(kind=KIND, variables=0, union_width=0,
                     nodes=[dict(op='input', clause=0, scope=[], table=0)], root=0)
        self.assertTrue(check_relation_proof(0, [()], empty))
        self.assertFalse(check_relation_proof(0, [], empty))

    def test_all_two_bit_formulas_against_original_truth_tables(self):
        clauses = [(), (1,), (-1,), (2,), (-2,),
                   (1, 2), (1, -2), (-1, 2), (-1, -2)]
        for mask in range(1 << len(clauses)):
            cs = [c for j, c in enumerate(clauses) if mask >> j & 1]
            guide = resolution_refute(2, cs, width=2)
            if guide['status'] != 'UNSAT':
                continue
            out = resolution_to_relations(2, cs, guide['certificate'])
            self.assertTrue(check_relation_proof(2, cs, out['certificate']))
            for bits in product((False, True), repeat=2):
                self.assertFalse(all(any(bits[abs(l)-1] == (l > 0) for l in c) for c in cs))
