import copy
from itertools import product
import unittest

from pnp_lab.affine_dag_pc import (DAG_KIND, boolean_zero_pc, clause_indicator,
    masked_affine_dag_pc, poly_mul, raw_affine_clause, replay_affine_dag)
from pnp_lab.parity_pc import ONE, replay_parity_pc
from experiments.affine_dag_pc import rank_cut_fixture, run


class AffineDAGPCTests(unittest.TestCase):
    def test_ordinary_boolean_correction_and_nonzero_rejection(self):
        value = frozenset({(1, 1, 2), (1, 2)})
        proof = boolean_zero_pc(2, value)
        self.assertEqual(proof['degree'], 3)
        self.assertEqual(replay_parity_pc(2, [], proof)['root'], value)
        with self.assertRaises(ValueError):
            boolean_zero_pc(2, ONE)
        with self.assertRaises(ValueError):
            boolean_zero_pc(2, [[1], [1]])
        with self.assertRaises(ValueError):
            boolean_zero_pc(-1, [])

    def test_repeated_and_inconsistent_affine_forms(self):
        value = clause_indicator(3, [((1, 2), 0), ((2, 3), 1), ((1, 3), 1)])
        self.assertEqual(value['rank'], 2)
        self.assertTrue(any(len(set(m)) < len(m) for m in value['polynomial']))
        self.assertIsNone(clause_indicator(1, [((1,), 0), ((1,), 1)])['rank'])
        self.assertEqual(clause_indicator(0, [])['polynomial'], ONE)
        with self.assertRaises(ValueError):
            clause_indicator(2, [((1, 1), 0)])

    def test_shared_dag_and_all_high_parent_cases(self):
        raw, dag = rank_cut_fixture()
        f = poly_mul(frozenset({(2,), (3,)}), frozenset({(2,), (4,)}))
        out = masked_affine_dag_pc(4, raw, dag, f, 1)
        self.assertEqual(replay_parity_pc(4, raw, out['certificate'])['root'], f)
        for case in ('zero_high_parents', 'one_high_parent', 'two_high_parents'):
            self.assertGreater(out['profile']['cases'][case], 0)
        self.assertGreater(out['profile']['shared_nodes'], 0)
        self.assertLessEqual(out['certificate']['degree'], 5)
        with self.assertRaises(ValueError):
            masked_affine_dag_pc(4, raw, dag, ONE, 1)

    def test_soundness_inputs_future_parents_and_caps(self):
        raw, dag = rank_cut_fixture()
        for node_ix, field, value in ((0, 'input', 1), (10, 'parents', [0]),
                                     (8, 'parents', [10]), (4, 'parents', [])):
            bad = copy.deepcopy(dag)
            bad['nodes'][node_ix][field] = value
            with self.assertRaises(ValueError):
                replay_affine_dag(4, raw, bad)
        with self.assertRaises(ValueError):
            replay_affine_dag(4, raw, dag, max_assignments=15)
        with self.assertRaises(ValueError):
            replay_affine_dag(4, raw, dag, max_semantic_work=1)
        with self.assertRaises(ValueError):
            masked_affine_dag_pc(4, raw, dag, [], 0)
        with self.assertRaises(ValueError):
            masked_affine_dag_pc(4, raw, dag, [(2,), (3,)], 1, max_nodes=0)

    def test_no_high_nodes_derives_one_and_changed_raw_is_rejected(self):
        raw = [(1,), (-1,)]
        dag = dict(kind=DAG_KIND, variables=1, nodes=[
            dict(op='input', input=i, clause=raw_affine_clause(c)) for i,c in enumerate(raw)]
            + [dict(op='infer', parents=[0, 1], clause=[])])
        proof = masked_affine_dag_pc(1, raw, dag, ONE, 1)['certificate']
        self.assertEqual(replay_parity_pc(1, raw, proof)['root'], ONE)
        with self.assertRaises(ValueError):
            replay_affine_dag(1, [(1,), (1,)], dag)

    def test_complete_small_audits(self):
        report = run()
        self.assertTrue(report['all_checks_passed'])
        self.assertEqual(report['summary']['boolean_ideal_basis_proofs'], 27)
        self.assertEqual(report['summary']['all_three_variable_affine_flats_checked'], 52)
