import copy
from itertools import product
import random
import unittest

from experiments.physical_restart_bridge import block_cnf
from experiments.retained_learning import check_answer, pigeonhole, signed_rename, split_cnf
from pnp_lab.resolution_closure import check_resolution
from pnp_lab.retained_learning import replay_trace, solve


def truth(clauses, bits):
    return all(any(bits[abs(lit)-1] == (lit > 0) for lit in clause) for clause in clauses)


class RetainedLearningTests(unittest.TestCase):
    def assert_oracle(self, n, clauses, retain):
        models = [bits for bits in product((False, True), repeat=n) if truth(clauses, bits)]
        answer = solve(n, clauses, retain=retain)
        check_answer(n, clauses, answer)
        self.assertEqual(answer['status'], 'SAT' if models else 'UNSAT')
        # Check every intermediate consequence, including those never retained.
        for positive, negative in replay_trace(n, clauses, answer['trace']):
            for bits in models:
                self.assertTrue(any((positive >> i & 1) and bits[i] or
                                    (negative >> i & 1) and not bits[i] for i in range(n)))
        if answer['status'] == 'SAT':
            bits = tuple(bool(answer['witness'] >> i & 1) for i in range(n))
            self.assertTrue(truth(clauses, bits))
        else:
            self.assertTrue(check_resolution(n, clauses, answer['certificate']))
        return answer

    def test_all_two_variable_formulas_both_modes(self):
        universe = ((1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2))
        for mask in range(1 << len(universe)):
            clauses = tuple(c for i, c in enumerate(universe) if mask >> i & 1)
            for retain in (False, True):
                self.assert_oracle(2, clauses, retain)
        for retain in (False, True):
            self.assert_oracle(0, (), retain)
            self.assert_oracle(0, ((),), retain)

    def test_small_mixed_width_formulas_independently(self):
        rng = random.Random(73103)
        for n in range(3, 7):
            for _ in range(20):
                clauses = []
                for _ in range(rng.randrange(1, 5*n)):
                    scope = rng.sample(range(1, n+1), rng.randrange(1, 4))
                    clauses.append(tuple(v if rng.getrandbits(1) else -v for v in scope))
                for retain in (False, True):
                    self.assert_oracle(n, clauses, retain)

    def test_corrupted_resolution_traces_and_refutations_rejected(self):
        clauses = ((1, 2), (1, -2), (-1, 2), (-1, -2))
        answer = solve(2, clauses)
        for field, value in (('pivot', 0), ('left', 999), ('right', -1), ('op', 'oracle')):
            trace = copy.deepcopy(answer['trace'])
            index = next(i for i, node in enumerate(trace) if node['op'] == 'resolve')
            trace[index][field] = value
            with self.assertRaises(ValueError):
                replay_trace(2, clauses, trace)
        proof = copy.deepcopy(answer['certificate'])
        proof['nodes'][-1]['pivot'] *= -1
        self.assertFalse(check_resolution(2, clauses, proof))
        trace = copy.deepcopy(answer['trace'])
        trace[0]['clause'] = -1
        with self.assertRaises(ValueError):
            replay_trace(2, clauses, trace)

    def test_width_three_split_preserves_existential_semantics(self):
        for n in range(1, 7):
            source = (tuple(v if v % 2 else -v for v in range(1, n+1)),)
            total, clauses = split_cnf(n, source)
            self.assertTrue(all(len(c) <= 3 for c in clauses))
            for bits in product((False, True), repeat=n):
                expanded = any(truth(clauses, bits+extra)
                               for extra in product((False, True), repeat=total-n))
                self.assertEqual(expanded, truth(source, bits))
        for holes in (1, 2):
            n, clauses = pigeonhole(holes)
            self.assertFalse(any(truth(clauses, bits) for bits in product((False, True), repeat=n)))

    def test_signed_renamed_physical_traps_have_checked_repairs(self):
        for blocks in (1, 2, 4):
            n, clauses = block_cnf(blocks, connected=True)
            for seed in (0, 1, 37):
                changed = signed_rename(n, clauses, seed)
                for retain in (False, True):
                    answer = solve(n, changed, retain=retain)
                    self.assertEqual(answer['status'], 'SAT')
                    self.assertEqual(answer['stats']['decisions'], blocks)
                    self.assertLessEqual(answer['stats']['conflicts'], blocks)
                    check_answer(n, changed, answer)

    def test_budget_exhaustion_preserves_valid_prefix_and_unknown(self):
        clauses = ((1, 2), (1, -2), (-1, 2), (-1, -2))
        for limits in ({'max_work': 0}, {'max_work': 25}, {'max_proof_nodes': 0},
                       {'max_proof_nodes': 4}, {'max_proof_literals': 0},
                       {'max_learned_literals': 0}, {'max_depth': 0}):
            answer = solve(2, clauses, **limits)
            self.assertEqual(answer['status'], 'UNKNOWN', limits)
            check_answer(2, clauses, answer)
            for parameter, value in limits.items():
                key = dict(max_work='work', max_proof_nodes='proof_nodes',
                           max_proof_literals='proof_literal_slots',
                           max_learned_literals='learned_literal_slots',
                           max_depth='maximum_depth')[parameter]
                self.assertLessEqual(answer['stats'][key], value)

    def test_both_modes_backtrack_over_irrelevant_decisions(self):
        n = 10
        u, v = n-1, n
        clauses = ((u, v), (u, -v), (-u, v), (-u, -v))
        clauses += tuple((x, u, v) for x in range(1, n-1))
        for retain in (False, True):
            answer = solve(n, clauses, retain=retain)
            self.assertEqual(answer['status'], 'UNSAT')
            self.assertEqual(answer['stats']['conflicts'], 2)
            self.assertGreater(answer['stats']['skipped_sibling_branches'], 0)
            check_answer(n, clauses, answer)

    def test_retention_counter_and_work_accounting(self):
        n, clauses = block_cnf(2, connected=True)
        work_keys = ('literal_inspections', 'resolution_literal_visits', 'proof_record_visits',
                     'assignment_copy_visits', 'decision_work', 'witness_literal_visits')
        for retain in (False, True):
            answer = solve(n, clauses, retain=retain)
            stats = answer['stats']
            self.assertEqual(stats['work'], sum(stats[key] for key in work_keys))
            self.assertLessEqual(stats['work'], 200_000)
            self.assertGreater(stats['proof_nodes'], len(clauses))
            if retain:
                self.assertGreater(stats['learned_clauses'], 0)
            else:
                self.assertEqual(answer['learned'], [])
                self.assertEqual(stats['learned_literal_slots'], 0)
            replayed = replay_trace(n, clauses, answer['trace'])
            self.assertEqual(stats['proof_literal_slots'], sum(p.bit_count()+q.bit_count() for p, q in replayed))

    def test_duplicate_inputs_and_unused_variables(self):
        clauses = ((1,), (1,), (-1, 2))
        for retain in (False, True):
            answer = self.assert_oracle(3, clauses, retain)
            self.assertEqual(answer['witness'], 3)

    def test_invalid_input_and_caps(self):
        for n, clauses in ((-1, ()), (1, ((0,),)), (1, ((1, -1),)), (4, ((1, 2, 3, 4),))):
            with self.assertRaises(ValueError):
                solve(n, clauses)
        for name in ('max_work', 'max_proof_literals', 'max_proof_nodes', 'max_learned_literals', 'max_depth'):
            for value in (-1, True, 1.5):
                with self.assertRaises(ValueError):
                    solve(0, (), **{name: value})
        with self.assertRaises(ValueError):
            solve(0, (), retain=1)


if __name__ == '__main__':
    unittest.main()
