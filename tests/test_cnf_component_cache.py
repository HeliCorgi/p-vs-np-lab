from itertools import product
import unittest

from experiments.mcsp_counterexample_search import semantic_catalog
from pnp_lab.cnf_component_cache import ComponentSolver, search_shared
from pnp_lab.mcsp_counterexample import witness_table


def brute(clauses, assumptions):
    variables = sorted({abs(lit) for clause in clauses for lit in clause} | set(assumptions))
    for bits in product((False, True), repeat=len(variables)):
        model = dict(zip(variables, bits))
        if all(model[v] == bit for v, bit in assumptions.items()) and all(
                any(model[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses):
            return model
    return None


def copies(count):
    return tuple(clause for i in range(count) for clause in ((2*i+1, 2*i+2), (-2*i-1, 2*i+2)))


class ComponentCacheTests(unittest.TestCase):
    def test_every_two_variable_cnf_and_assumption(self):
        available = tuple(tuple((i+1)*value for i, value in enumerate(pattern) if value)
                          for pattern in product((-1, 0, 1), repeat=2) if any(pattern))
        solver = ComponentSolver(max_cache_cells=None)
        for mask in range(256):
            clauses = tuple(clause for i, clause in enumerate(available) if mask >> i & 1)
            for pattern in product((-1, 0, 1), repeat=2):
                assumptions = {i+1: value == 1 for i, value in enumerate(pattern) if value}
                result = solver.solve(clauses, assumptions=assumptions, max_work=None)
                expected = brute(clauses, assumptions)
                self.assertEqual(result['status'] == 'YES', expected is not None)
                if expected is not None:
                    model = result['model']
                    self.assertTrue(all(model.get(v, False) == bit for v, bit in assumptions.items()))
                    self.assertTrue(all(any(model.get(abs(lit), False) == (lit > 0) for lit in clause)
                                        for clause in clauses))

    def test_model_is_transferred_under_renaming(self):
        solver = ComponentSolver()
        solver.solve(((1, 2), (-1, 2)), max_work=None)
        result = solver.solve(((70, 90), (-70, 90)), max_work=None)
        self.assertEqual(result['status'], 'YES')
        self.assertTrue(result['model'][90])
        self.assertEqual(result['metrics']['computed_states'], 0)
        self.assertEqual(result['metrics']['nontrivial_cache_hits'], 1)

    def test_increasing_evidence_does_not_reuse_an_invalid_answer(self):
        solver = ComponentSolver()
        formula = ((1, 2),)
        self.assertEqual(solver.solve(formula)['status'], 'YES')
        self.assertEqual(solver.solve(formula, assumptions={1: False, 2: False})['status'], 'NO')
        self.assertEqual(solver.solve(formula, assumptions={1: False, 2: True})['status'], 'YES')

    def test_independent_components_and_connected_contradiction(self):
        solver = ComponentSolver(max_cache_cells=None)
        result = solver.solve(copies(64), max_work=None)
        self.assertEqual(result['status'], 'YES')
        self.assertEqual(result['metrics']['completed_states'], 3)
        self.assertEqual(result['metrics']['nontrivial_cache_hits'], 63)
        self.assertTrue(all(result['model'][2*i+2] for i in range(64)))
        connected = copies(2) + ((-2, -4),)
        self.assertEqual(solver.solve(connected, max_work=None)['status'], 'NO')

    def test_unsat_result_reuse_and_capacity_fallback(self):
        contradiction = ((1, 2), (1, -2), (-1, 2), (-1, -2))
        solver = ComponentSolver(max_cache_cells=None)
        self.assertEqual(solver.solve(contradiction, max_work=None)['status'], 'NO')
        renamed = tuple(tuple((10 if abs(lit)==1 else 20)*(1 if lit>0 else -1) for lit in c)
                        for c in contradiction)
        result = solver.solve(renamed, max_work=None)
        self.assertEqual(result['status'], 'NO')
        self.assertEqual(result['metrics']['computed_states'], 0)
        small = ComponentSolver(max_cache_cells=0)
        self.assertEqual(small.solve(contradiction, max_work=None)['status'], 'NO')
        self.assertEqual(small.cache_cells, 0)

    def test_unknown_never_becomes_a_cached_no(self):
        solver = ComponentSolver()
        self.assertEqual(solver.solve(copies(8), max_work=10)['status'], 'UNKNOWN')
        self.assertEqual(solver.solve(copies(8), max_work=None)['status'], 'YES')
        for formula, (packed, _) in solver.cache.items():
            if packed is not None:
                self.assertTrue(all(any(packed[abs(lit)-1] == (lit>0) for lit in clause) for clause in formula))
            elif len({abs(l) for c in formula for l in c}) <= 4:
                self.assertIsNone(brute(formula, {}))

    def test_all_two_input_mcsp_targets_without_cap(self):
        feasible = semantic_catalog(2, 2)
        for table in range(16):
            for cache in (False, True):
                result = search_shared(2, 2, table, cache=cache, max_work_per_extract=None)
                self.assertEqual(result['status'] == 'YES', table in feasible)
                if result['witness']:
                    self.assertEqual(witness_table(result['witness']), table)

    def test_tautologies_empty_clauses_and_untrusted_ordering(self):
        solver = ComponentSolver()
        self.assertEqual(solver.solve(((1, -1),))['status'], 'YES')
        self.assertEqual(solver.solve(((),))['status'], 'NO')
        result = solver.solve(((-1,),), decision_order=lambda context, meter: [(1, 99)])
        self.assertEqual(result['status'], 'YES')
        self.assertFalse(result['model'][1])
        result = solver.solve(((-1, 2), (-1, -2), (1, 2)),
                              decision_order=lambda context, meter: [(1,)])
        self.assertEqual(result['status'], 'YES')
        self.assertFalse(result['model'][1])
        with self.assertRaises(ValueError):
            solver.solve(((0,),))


if __name__ == '__main__':
    unittest.main()
