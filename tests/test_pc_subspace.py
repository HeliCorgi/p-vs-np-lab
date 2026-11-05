import copy
from itertools import combinations, combinations_with_replacement, product
import unittest

from pnp_lab.pc_subspace import (check_pc_subspace, check_static_moment,
                                 pc_subspace, replay_pc_subspace)


def small_brute_space(n, clauses, bound):
    """Enumerate all polynomials in the closure; no Gaussian elimination."""
    monomials = [m for degree in range(bound + 1)
                 for m in combinations_with_replacement(range(1, n + 1), degree)]
    columns = {m: i for i, m in enumerate(monomials)}

    def encode(terms):
        row = 0
        for term in terms:
            row ^= 1 << columns[term]
        return row

    space = {0}

    def add(row):
        space.update([row ^ old for old in space])

    for clause in clauses:
        if len(clause) > bound:
            continue
        positive = [v for v in clause if v > 0]
        negative = [-v for v in clause if v < 0]
        terms = [tuple(sorted(negative + [v for v, b in zip(positive, bits) if b]))
                 for bits in product((0, 1), repeat=len(positive))]
        add(encode(terms))
    if bound >= 2:
        for variable in range(1, n + 1):
            add(encode([(variable,), (variable, variable)]))
    while True:
        old_size = len(space)
        for row in list(space):
            terms = [m for i, m in enumerate(monomials) if row >> i & 1]
            if max(map(len, terms), default=0) >= bound:
                continue
            for variable in range(1, n + 1):
                add(encode(tuple(sorted((*m, variable))) for m in terms))
        if len(space) == old_size:
            break
    return monomials, space


def php_three_two():
    return [(1, 2), (3, 4), (5, 6)] + [
        (-2*i-a, -2*j-a) for a in (1, 2) for i, j in combinations(range(3), 2)]


class PCSubspaceTests(unittest.TestCase):
    def test_every_two_variable_cnf_against_enumerated_polynomial_space(self):
        possible = [(), (1,), (-1,), (2,), (-2,)]
        possible += list(product((1, -1), (2, -2)))
        for chosen in range(1 << len(possible)):
            clauses = [c for i, c in enumerate(possible) if chosen >> i & 1]
            models = sum(all(any(bool(word >> (abs(lit)-1) & 1) == (lit > 0)
                                 for lit in c) for c in clauses) for word in range(4))
            for bound in (0, 1, 2):
                answer = pc_subspace(2, clauses, bound=bound)
                self.assertEqual(answer['status'], 'COMPLETE')
                self.assertTrue(check_pc_subspace(2, clauses, answer['certificate']))
                monomials, space = small_brute_space(2, clauses, bound)
                profile = answer['profile']
                self.assertEqual(profile['basis_rank'], len(space).bit_length()-1)
                self.assertEqual(profile['refutes'], 1 in space)
                if bound == 2:
                    self.assertEqual(profile['separated_dimension'], models)
                if answer['static_separator'] is not None:
                    self.assertTrue(check_static_moment(2, clauses, answer['static_separator']))

    def test_pc_closes_degree_falls_which_static_macaulay_misses(self):
        raw = [(-1, -2), (-1, 2)]
        answer = pc_subspace(3, raw, bound=2)
        self.assertEqual((answer['profile']['static_basis_rank'],
                          answer['profile']['basis_rank']), (5, 6))
        check = replay_pc_subspace(3, raw, answer['certificate'], generators=[[[1, 3]]])
        self.assertEqual(check['candidate']['intersection_dimension'], 1)
        php = php_three_two()
        low = pc_subspace(6, php, bound=2)
        high = pc_subspace(6, php, bound=3)
        self.assertFalse(low['profile']['refutes'])
        self.assertTrue(high['profile']['refutes'])
        self.assertFalse(high['profile']['static_refutes'])
        self.assertEqual((high['profile']['basis_rank'], high['profile']['static_basis_rank']),
                         (84, 82))
        self.assertTrue(check_static_moment(6, php, high['static_separator']))
        bad = copy.deepcopy(high['static_separator'])
        bad['one_monomials'].remove([])
        self.assertFalse(check_static_moment(6, php, bad))
        self.assertFalse(check_static_moment(6, php + [()], high['static_separator']))

    def test_forced_variable_padding_preserves_separated_dimension_and_degree(self):
        core = php_three_two()
        padded = core + [(-7,), (-8,), (-9,)]
        a = pc_subspace(6, core, bound=2, target_degree=2)
        b = pc_subspace(9, padded, bound=2, target_degree=2)
        self.assertEqual(a['profile']['separated_dimension'], 13)
        self.assertEqual(b['profile']['separated_dimension'], 13)
        self.assertEqual((a['profile']['low_degree_dimension'],
                          b['profile']['low_degree_dimension']), (28, 55))
        self.assertTrue(check_pc_subspace(9, padded, b['certificate']))
        self.assertTrue(pc_subspace(9, padded, bound=3)['profile']['refutes'])
        self.assertFalse(b['profile']['refutes'])

    def test_separation_of_a_span_requires_more_than_its_individual_generators(self):
        raw = [(1, 2, 3)]
        answer = pc_subspace(3, raw, bound=3)
        monomials = [list(m) for k in range(4) for m in combinations((1, 2, 3), k)]
        for monomial in monomials:
            replay = replay_pc_subspace(3, raw, answer['certificate'], generators=[[monomial]])
            self.assertTrue(replay['candidate']['separated'])
        replay = replay_pc_subspace(3, raw, answer['certificate'],
                                    generators=[[m] for m in monomials])
        self.assertEqual(replay['candidate']['dimension'], 8)
        self.assertEqual(replay['candidate']['intersection_dimension'], 1)
        self.assertFalse(replay['candidate']['separated'])
        # Removing the full clause-support monomial gives the empty-support
        # space for this single-clause control.
        replay = replay_pc_subspace(3, raw, answer['certificate'],
                                    generators=[[m] for m in monomials[:-1]])
        self.assertTrue(replay['candidate']['separated'])

    def test_completeness_raw_binding_and_allows_no_implicit_boolean_quotient(self):
        raw = [(-1, -2), (-1, 2)]
        answer = pc_subspace(3, raw, bound=2)
        cert = answer['certificate']
        self.assertFalse(check_pc_subspace(3, raw + [()], cert))
        self.assertFalse(check_pc_subspace(3, raw, cert, bound=3))
        for field, value in (('kind', 'fake'), ('field', True), ('bound', 1),
                             ('target_degree', False), ('variables', 4), ('basis', []),
                             ('separated_monomials', [])):
            self.assertFalse(check_pc_subspace(3, raw, dict(cert, **{field: value})))
        for i in range(len(cert['basis'])):
            bad = copy.deepcopy(cert)
            bad['basis'].pop(i)
            self.assertFalse(check_pc_subspace(3, raw, bad))
        bad = copy.deepcopy(cert)
        bad['basis'][0] = True
        self.assertFalse(check_pc_subspace(3, raw, bad))
        # Drop precisely the dynamically generated x*z row, then adjust the
        # advertised complement.  A checker must still reject lack of closure.
        from pnp_lab.parity_pc import replay_parity_pc
        polynomials = replay_parity_pc(3, raw, cert['trace'])['polynomials']
        bad = copy.deepcopy(cert)
        bad['basis'] = [i for i in bad['basis'] if polynomials[i] != frozenset({(1, 3)})]
        bad['separated_monomials'] = [[], [2], [3], [1, 3], [2, 3]]
        self.assertFalse(check_pc_subspace(3, raw, bad))
        powers = pc_subspace(1, [], bound=3)
        self.assertEqual(powers['profile']['ambient_dimension'], 4)
        self.assertEqual(powers['profile']['separated_dimension'], 2)
        self.assertTrue(check_pc_subspace(1, [], powers['certificate']))

    def test_boundary_cases_omitted_axioms_and_explicit_budget_status(self):
        self.assertFalse(pc_subspace(0, [], bound=0)['profile']['refutes'])
        self.assertTrue(pc_subspace(0, [()], bound=0)['profile']['refutes'])
        huge_constant_space = pc_subspace(10**20, [], bound=0)
        self.assertEqual(huge_constant_space['status'], 'COMPLETE')
        self.assertEqual(huge_constant_space['profile']['ambient_dimension'], 1)
        self.assertTrue(check_pc_subspace(10**20, [], huge_constant_space['certificate']))
        sparse = pc_subspace(10**9, [(10**9,)], bound=0)
        self.assertEqual(sparse['profile']['omitted_clause_axioms'], 1)
        self.assertEqual(sparse['profile']['separated_dimension'], 1)
        self.assertTrue(check_pc_subspace(10**9, [(10**9,)], sparse['certificate']))
        omitted = pc_subspace(3, [(-1,), (-2,), (-3,), (1, 2, 3)], bound=2)
        self.assertEqual(omitted['profile']['separated_dimension'], 1)
        self.assertEqual(omitted['profile']['omitted_clause_axioms'], 1)
        raw = [(-1, -2), (-1, 2)]
        for limits in ({'max_monomials': 0}, {'max_nodes': 0},
                       {'max_trace_terms': 0}, {'max_work': 0}):
            answer = pc_subspace(3, raw, bound=2, **limits)
            self.assertEqual(answer['status'], 'UNKNOWN')
            self.assertIsNone(answer['certificate'])
            self.assertTrue(answer['profile']['budget_limited'])
        huge = pc_subspace(10**9, [], bound=10**9)
        self.assertEqual(huge['status'], 'UNKNOWN')
        repeated = pc_subspace(1, [(1,)*24], bound=24)
        self.assertEqual(repeated['status'], 'UNKNOWN')
        for bad in ({'bound': True}, {'bound': -1}, {'bound': 2, 'target_degree': 3},
                    {'bound': 2, 'max_work': False}):
            with self.assertRaises(ValueError):
                pc_subspace(3, raw, **bad)


if __name__ == '__main__':
    unittest.main()
