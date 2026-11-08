"""Independent CNF semantics, gate corruption, and finite suffix audits."""
import json
from pathlib import Path
import unittest

from experiments.tseitin_affine_lift import build_cnf, eval_clause
from experiments.tseitin_obdd_boundary import (build_obdd, ordered_variables, accept,
                                  node_stats, accepting_assignments_by_dp,
                                  x_first_residual_signatures, verify)


class TseitinOBDDBoundaryTests(unittest.TestCase):
    def test_exact_raw_cnf_oracle_m1_to_m3(self):
        for m in (1, 2, 3):
            graph = build_obdd(m)
            n, clauses, _ = build_cnf(m)
            for z in range(1 << n):
                self.assertEqual(accept(graph, z), all(eval_clause(c, z) for c in clauses),
                                 (m, z))

    def test_independent_dynamic_path_count(self):
        for m in (1, 2, 3):
            graph = build_obdd(m)
            brute = sum(accept(graph, z) for z in range(1 << (4*m-1)))
            self.assertEqual(accepting_assignments_by_dp(graph), brute)
            self.assertEqual(brute, (2**m-1) * 2**(m-1))

    def test_live_width_counts_and_read_once_order(self):
        for m in (1, 2, 3):
            graph = build_obdd(m)
            self.assertEqual(sorted(v for _, _, v in ordered_variables(m)),
                             list(range(1,4*m)))
            counts = (1, 2, 2) + (2, 4, 4, 2) * (m-1)
            self.assertEqual(tuple(len(s) for s in graph['states'][:-1]), counts)
            self.assertEqual(node_stats(graph)['nonterminal_nodes'], 12*m-7)
            self.assertLessEqual(node_stats(graph)['max_live_width'], 4)
            self.assertEqual(len(graph['edges']), 12*m-7)
            for depth, s in enumerate(graph['states'][:-1]):
                for state in s:
                    self.assertEqual(len(graph['edges'][(depth, state)]), 2)

    def test_every_inconsistent_gate_or_output_rejected(self):
        for m in (1, 2, 3):
            graph = build_obdd(m)
            n, clauses, _ = build_cnf(m)
            originals_mask = (1<<(2*m))-1
            sat = [z for z in range(1<<n) if all(eval_clause(c,z) for c in clauses)]
            self.assertTrue(sat)
            for z in sat:
                for gate_var in range(2*m+1, n+1):
                    corrupted = z ^ (1 << (gate_var-1))
                    self.assertEqual(z & originals_mask, corrupted & originals_mask)
                    self.assertFalse(accept(graph, corrupted), (m,z,gate_var))

    def test_x_first_residuals_distinct_and_zero_branch_dead(self):
        for m in (1, 2, 3):
            signs = x_first_residual_signatures(m)
            self.assertEqual(len(signs), 1 << m)
            self.assertEqual(len(set(signs)), 1 << m)
            self.assertEqual(signs[0], ())
            self.assertTrue(all(signs[x] for x in range(1,1<<m)))
            for x in range(1,1<<m):
                for y in range(x+1,1<<m):
                    self.assertTrue(set(signs[x]) ^ set(signs[y]))

    def test_precommitted_finite_snapshot(self):
        report = json.loads((Path(__file__).resolve().parents[1] / 'results' /
                             'tseitin_obdd_boundary.json').read_text(encoding='utf-8'))
        self.assertEqual(report['results'], [verify(m) for m in (1, 2, 3)])

    def test_budget_and_out_of_range_inputs(self):
        with self.assertRaises(ValueError):
            ordered_variables(0)
        with self.assertRaises(ValueError):
            verify(4)
        with self.assertRaises(ValueError):
            x_first_residual_signatures(4)
        with self.assertRaises(ValueError):
            accept(build_obdd(1), -1)
        with self.assertRaises(ValueError):
            accept(build_obdd(1), 8)

if __name__ == '__main__':
    unittest.main()
