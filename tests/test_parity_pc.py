import copy
from itertools import product
import unittest

from pnp_lab.parity_pc import (KIND, check_parity_pc, discharge_parity_pc,
                               glue_parity_pc, parity_tree_to_pc, replay_parity_pc)
from pnp_lab.parity_query import KIND as TREE_KIND, parity_query_refute


def certificate(n, degree, nodes):
    return dict(kind=KIND, field=2, variables=n, degree=degree,
                nodes=nodes, root=len(nodes)-1)


class ParityPCTests(unittest.TestCase):
    def test_ordinary_powers_are_not_implicitly_reduced(self):
        proof = certificate(1, 3, [dict(op='boolean', variable=1),
                                   dict(op='multiply', parent=0, variable=1)])
        result = replay_parity_pc(1, [], proof)
        self.assertEqual(result['root'], frozenset({(1, 1, 1), (1, 1)}))
        self.assertEqual(result['profile']['proof_degree'], 3)
        with self.assertRaises(ValueError):
            replay_parity_pc(1, [], dict(proof, degree=2))
        self.assertFalse(check_parity_pc(1, [], proof))

    def test_discharge_affine_constant_and_no_hidden_assumption(self):
        source = certificate(1, 1, [dict(op='assumption', index=0),
                                    dict(op='assumption', index=1),
                                    dict(op='add', left=0, right=1)])
        assumptions = [([1], 0), ([1], 1)]
        self.assertTrue(check_parity_pc(1, [], source, assumptions=assumptions))
        self.assertFalse(check_parity_pc(1, [], source))
        for index, target in ((0, frozenset({(), (1,)})), (1, frozenset({(1,)}))):
            proof = discharge_parity_pc(1, [], source, assumptions=assumptions, index=index)
            remaining = assumptions[:index] + assumptions[index+1:]
            result = replay_parity_pc(1, [], proof, assumptions=remaining)
            self.assertEqual(result['root'], target)
            self.assertLessEqual(proof['degree'], 2)
            self.assertFalse(check_parity_pc(1, [], proof, assumptions=remaining))
        with self.assertRaises(ValueError):
            discharge_parity_pc(1, [], source, assumptions=assumptions, index=True)

    def test_general_leaf_glue_retains_only_ancestor_context(self):
        raw = [(1,), (-1, 2)]
        context = [([2], 0)]
        left = certificate(2, 1, [dict(op='input', clause=0), dict(op='assumption', index=1),
                                  dict(op='add', left=0, right=1)])
        right = certificate(2, 2, [dict(op='input', clause=1),
                                   dict(op='assumption', index=0),
                                   dict(op='multiply', parent=1, variable=1),
                                   dict(op='add', left=0, right=2),
                                   dict(op='assumption', index=1),
                                   dict(op='add', left=3, right=4)])
        for ranks in ((2, 2), (3, 2)):
            result = glue_parity_pc(2, raw, [1], left, right, assumptions=context,
                                    zero_rank=ranks[0], one_rank=ranks[1])
            proof = result['certificate']
            self.assertTrue(check_parity_pc(2, raw, proof, assumptions=context))
            self.assertFalse(check_parity_pc(2, raw, proof))
            self.assertFalse(check_parity_pc(2, raw, proof, assumptions=[([2], 1)]))
            self.assertEqual(result['discharged_branch'], int(ranks[1] < ranks[0]))
            self.assertLessEqual(proof['degree'], result['rank'])
        with self.assertRaises(ValueError):
            glue_parity_pc(2, raw, [1], left, right, assumptions=context, one_rank=1)

    def test_balanced_wide_queries_and_nonuniform_comb_ranks(self):
        raw = list(product((1, -1), (2, -2), (3, -3)))
        tree = parity_query_refute(3, raw)['certificate']
        out = parity_tree_to_pc(3, raw, tree)
        self.assertEqual(out['status'], 'UNSAT')
        self.assertEqual((out['stats']['certified_rank'], out['certificate']['degree']), (6, 6))
        self.assertEqual(out['stats']['weighted_leaf_mass'], 64)
        self.assertTrue(check_parity_pc(3, raw, out['certificate'], max_degree=6))
        self.assertFalse(check_parity_pc(3, raw, out['certificate'], max_degree=5))
        self.assertTrue(all(node['op'] != 'assumption' for node in out['certificate']['nodes']))
        raw = [(1,), (-1, 2), (-1, -2, 3), (-1, -2, -3)]
        tree = dict(kind=TREE_KIND, root=0, nodes=[
            dict(query=[1], zero=1, one=2), dict(clause=0),
            dict(query=[2], zero=3, one=4), dict(clause=1),
            dict(query=[3], zero=5, one=6), dict(clause=2), dict(clause=3)])
        out = parity_tree_to_pc(3, raw, tree)
        self.assertEqual(out['stats']['actual_leaf_degree_histogram'], {'1': 1, '2': 1, '3': 2})
        self.assertEqual((out['stats']['certified_rank'], out['stats']['weighted_leaf_mass']), (4, 24))
        self.assertEqual(out['stats']['leaf_count_degree_bound'], 5)
        self.assertEqual(out['certificate']['degree'], 4)
        self.assertTrue(check_parity_pc(3, raw, out['certificate']))

    def test_raw_binding_malformed_nodes_and_caps(self):
        raw = list(product((1, -1), (2, -2)))
        tree = parity_query_refute(2, raw)['certificate']
        proof = parity_tree_to_pc(2, raw, tree)['certificate']
        self.assertFalse(check_parity_pc(2, [tuple(abs(v) for v in c) for c in raw], proof))
        for field, value in (('kind', 'fake'), ('field', 3), ('field', True),
                             ('degree', proof['degree']-1), ('degree', proof['degree']+1),
                             ('root', False), ('root', 0), ('nodes', [])):
            self.assertFalse(check_parity_pc(2, raw, dict(proof, **{field: value})))
        for operation in ('input', 'boolean', 'add', 'multiply'):
            bad = copy.deepcopy(proof)
            ix = next(i for i, node in enumerate(bad['nodes']) if node['op'] == operation)
            node = bad['nodes'][ix]
            if operation == 'input': node['clause'] = len(raw)
            elif operation == 'boolean': node['variable'] = True
            elif operation == 'add': node['left'] = ix
            else: node['variable'] = 3
            self.assertFalse(check_parity_pc(2, raw, bad), operation)
        for limits in ({'max_nodes': 0}, {'max_monomials': 0}):
            out = parity_tree_to_pc(2, raw, tree, **limits)
            self.assertEqual(out['status'], 'UNKNOWN')
            self.assertIsNone(out['certificate'])
            self.assertTrue(out['stats']['budget_limited'])
        with self.assertRaises(ValueError):
            parity_tree_to_pc(2, raw, tree, max_nodes=True)


if __name__ == '__main__':
    unittest.main()
