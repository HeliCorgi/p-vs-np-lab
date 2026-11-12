"""Independent dense operators, rational interpolation, and finite optimization."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
import unittest

from experiments.eth_polynomial_repair import (
    RepairBudgetExceeded, balance_requirements, evaluate, interpolate, lower_bounds, optimize,
    optimistic_retuning, rank_defect, taylor_calls, weights,
)


def dense_operator(r, q, nodes, coefficients):
    """Build columns of V*f(W) directly from permutations, without eigenvalues."""
    labels = list(product(range(r), repeat=2*q))
    positions = {label: i for i, label in enumerate(labels)}
    swaps = []
    for s in range(q):
        permutation = []
        for label in labels:
            row = list(label)
            row[2*s], row[2*s+1] = row[2*s+1], row[2*s]
            permutation.append(positions[tuple(row)])
        swaps.append(permutation)
    complete = [positions[tuple(label[j ^ 1] for j in range(2*q))] for label in labels]
    dimension = len(labels)
    matrix = [[F(0) for _ in labels] for _ in labels]
    for column in range(dimension):
        unit = [F(int(i == column)) for i in range(dimension)]
        vector = [coefficients[-1]*v for v in unit]
        for k in range(len(coefficients)-2, -1, -1):
            w_vector = [(q*vector[i]-sum(vector[permutation[i]] for permutation in swaps))/2
                        for i in range(dimension)]
            vector = [w_vector[i]-nodes[k]*vector[i]+coefficients[k]*unit[i]
                      for i in range(dimension)]
        for row in range(dimension):
            matrix[row][column] = vector[complete[row]]
    return labels, matrix


def rational_rank(matrix):
    a = [row[:] for row in matrix]
    pivot_row = 0
    for column in range(len(a[0])):
        pivot = next((j for j in range(pivot_row, len(a)) if a[j][column]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        scale = a[pivot_row][column]
        a[pivot_row] = [v/scale for v in a[pivot_row]]
        for j in range(pivot_row+1, len(a)):
            multiple = a[j][column]
            if multiple:
                a[j] = [x-multiple*y for x, y in zip(a[j], a[pivot_row])]
        pivot_row += 1
    return pivot_row


class ETHPolynomialRepairTests(unittest.TestCase):
    def test_dense_swaps_match_spectral_rank_and_support_bound(self):
        for r, q in ((2, 1), (2, 2), (2, 3), (3, 1)):
            for degree in range(q+1):
                nodes = tuple(range(degree+1))
                coefficients = interpolate(nodes)
                labels, matrix = dense_operator(r, q, nodes, coefficients)
                defect = [[F(i == j)-entry for j, entry in enumerate(row)]
                          for i, row in enumerate(matrix)]
                self.assertEqual(rational_rank(defect), rank_defect(r, q, nodes, coefficients))
                for i, row in enumerate(matrix):
                    for j, entry in enumerate(row):
                        if entry:
                            mismatches = sum(labels[j][2*s] != labels[i][2*s+1] for s in range(q))
                            self.assertLessEqual(mismatches, degree)

    def test_newton_matches_independent_lagrange_interpolation(self):
        for nodes in ((0,), (0, 2), (0, 1, 2), (3, 4, 6), (4, 1, 3, 0)):
            coefficients = interpolate(nodes)
            for x in range(10):
                expected = F(0)
                for node in nodes:
                    term = F((-1)**node)
                    for other in nodes:
                        if other != node:
                            term *= F(x-other, node-other)
                    expected += term
                self.assertEqual(evaluate(nodes, coefficients, x), expected)

    def test_optimum_for_constants_linear_and_full_degree(self):
        for r in (2, 3, 4):
            for q in range(1, 8):
                w = weights(r, q)
                total = r**(2*q)
                parity_best = (total+r**q)//2
                self.assertEqual(sum(w), total)
                self.assertEqual(optimize(q, 0, groups=(r,))[0]['optimum']['rank_defect'], total-parity_best)
                # A nonconstant line matches at most two, necessarily opposite signs.
                line_best = max(parity_best, max(w[i]+w[j] for i, j in combinations(range(q+1), 2)
                                                  if (i-j) % 2))
                self.assertEqual(optimize(q, 1, groups=(r,))[0]['optimum']['rank_defect'], total-line_best)
                self.assertEqual(optimize(q, q, groups=(r,))[0]['optimum']['rank_defect'], 0)

    def test_window_lower_bound_against_all_error_sets(self):
        for q in range(1, 8):
            w = weights(2, q)
            for degree in range(q+1):
                best = sum(w)
                for word in range(1 << (q+1)):
                    errors = {j for j in range(q+1) if word & (1 << j)}
                    if all(errors.intersection(range(start, start+degree+2))
                           for start in range(q-degree)):
                        best = min(best, sum(w[j] for j in errors))
                self.assertEqual(lower_bounds(2, q, degree)['consecutive_window'], best)

    def test_lower_bounds_for_independent_polynomial_grid(self):
        q, r = 7, 2
        w = weights(r, q)
        for coefficients in product(range(-2, 3), repeat=3):
            degree = max((i for i, c in enumerate(coefficients) if c), default=0)
            defect = sum(weight for j, weight in enumerate(w)
                         if sum(c*j**i for i, c in enumerate(coefficients)) != (-1)**j)
            self.assertLessEqual(lower_bounds(r, q, degree)['combined'], defect)

    def test_nonconsecutive_quadratic_improvement_independently(self):
        # f(j) = 5/3 - (2/3)*(j-5)^2; direct evaluation avoids Newton arithmetic.
        q, r = 12, 4
        w = [comb(q, j)*6**j*10**(q-j) for j in range(q+1)]
        matched = [j for j in range(q+1) if F(5, 3)-F(2, 3)*(j-5)**2 == (-1)**j]
        self.assertEqual(matched, [3, 4, 6, 7])
        defect = sum(w[j] for j in range(q+1) if j not in matched)
        self.assertEqual(defect, 104521901510656)
        # Every consecutive triple has f(j)=sign*(2*(j-center)^2-1),
        # and exactly those three matched spectral levels.
        baseline = min(sum(w[::2]), sum(w[1::2]),
                       min(sum(w)-sum(w[a:a+3]) for a in range(q-1)))
        self.assertEqual(baseline, 108217056710656)
        row = optimize(q, 2, groups=(r,))[0]
        self.assertEqual(row['optimum']['rank_defect'], defect)
        self.assertEqual(row['consecutive_or_constant_rank_defect'], baseline)
        self.assertGreater(baseline, defect)
        # Direct permutation matrices also check this polynomial at small Q.
        nodes = (3, 4, 6)
        _, matrix = dense_operator(2, 3, nodes, interpolate(nodes))
        residual = [[F(i == j)-v for j, v in enumerate(row)] for i, row in enumerate(matrix)]
        self.assertEqual(rational_rank(residual), rank_defect(2, 3, nodes, interpolate(nodes)))

    def test_taylor_counts_and_explicit_retuning_bound(self):
        for n in range(1, 9):
            for q in range(n+2):
                expected = sum(1 for word in product((0, 1, 2), repeat=n)
                               if sum(v != 0 for v in word) <= q)
                self.assertEqual(taylor_calls(n, q), expected)
        for n in range(6, 32):
            result = optimistic_retuning(n)
            minimum = None
            for r in (2, 3):
                for replacement_degree in (1, 2, 3):
                    for points in range(1, 2*n+1):
                        order = 3*n*replacement_degree//points
                        work = max(r**(2*points), taylor_calls(n, order))
                        bits = work.bit_length()-1
                        self.assertGreaterEqual(bits, result['all_size_guaranteed_log2_lower_bound'])
                        minimum = bits if minimum is None else min(minimum, bits)
            self.assertEqual(minimum, result['optimistic_optimum']['floor_log2_work_lower_bound'])

    def test_bad_inputs_and_budget_do_not_produce_optima(self):
        for r, q in ((1, 2), (-1, 2), (2, -1), (True, 2)):
            with self.assertRaises(ValueError):
                weights(r, q)
        for nodes in ((), (0, 0), (-1, 2), (True, 2)):
            with self.assertRaises(ValueError):
                interpolate(nodes)
        with self.assertRaises(RepairBudgetExceeded):
            optimize(12, 2, candidate_limit=285)
        self.assertEqual(optimize(12, 2, groups=(2,), candidate_limit=286)[0]['candidate_count'], 286)
        for q, d in ((3, 4), (-1, 0), (2, -1)):
            with self.assertRaises(ValueError):
                optimize(q, d)
        with self.assertRaises(ValueError):
            optimize(2, 1, groups=(2, 2))
        with self.assertRaises(ValueError):
            optimistic_retuning(5)

    def test_balance_conditions_force_large_groups_and_taylor_order(self):
        for n in (64, 256, 1024, 4096, 8192):
            bound = balance_requirements(n)
            count = 0
            for r in range(2, 65):
                for q in range(1, 7):
                    if 4*r**(4*q) <= n and 2*q*r*r <= n:
                        count += 1
                        self.assertLessEqual(q, bound['largest_possible_Q'])
                        self.assertGreaterEqual((n+r-1)//r, bound['largest_group_size_lower_bound'])
                        self.assertGreaterEqual(min(n, 3*n//q), bound['taylor_order_lower_bound'])
            self.assertGreater(count, 0)
        with self.assertRaises(ValueError):
            balance_requirements(63)


if __name__ == '__main__':
    unittest.main()
