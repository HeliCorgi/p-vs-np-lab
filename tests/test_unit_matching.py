import itertools
import random
import unittest
from functools import lru_cache, reduce
from operator import xor

from pnp_lab.unit_matching import (decide_unit_supports, lift_unit_choices, maximum_matching,
                           project_unit_matching, reduce_unit_supports)


def adjacency(n, edges):
    out = [[] for _ in range(n)]
    for i, j in edges:
        out[i].append(j)
        out[j].append(i)
    return out


def raw_max_size(neighbors):
    # Independent recurrence: leave the first remaining vertex unmatched, or
    # match it to one remaining neighbor. Only used by the finite test oracle.
    @lru_cache(None)
    def rec(vertices):
        if not vertices:
            return 0
        v = (vertices & -vertices).bit_length()-1
        rest = vertices & ~(1 << v)
        best = rec(rest)
        for w in neighbors[v]:
            if rest & (1 << w):
                best = max(best, 1 + rec(rest ^ (1 << w)))
        return best
    return rec((1 << len(neighbors))-1)


class UnitMatchingTests(unittest.TestCase):
    def test_all_simple_graphs_up_to_six_vertices(self):
        for n in range(7):
            all_edges = list(itertools.combinations(range(n), 2))
            for mask in range(1 << len(all_edges)):
                g = adjacency(n, [edge for k, edge in enumerate(all_edges) if mask >> k & 1])
                self.assertEqual(maximum_matching(g)["size"], raw_max_size(g), (n, mask))

    def test_graphs_with_overlapping_odd_cycles_against_raw_maximum(self):
        rng = random.Random(440279)
        for n in range(7, 13):
            for density in (0.15, 0.3, 0.5, 0.8):
                for _ in range(12):
                    edges = [e for e in itertools.combinations(range(n), 2)
                             if rng.random() < density]
                    g = adjacency(n, edges)
                    self.assertEqual(maximum_matching(g)["size"], raw_max_size(g), edges)

    def test_augmenting_path_through_contracted_triangle(self):
        # First pair 0-1. To match all four, root 2's search must reach 0-3:
        # 0 starts inner, but the triangle blossom makes it reachable as outer.
        g = adjacency(4, [(0, 1), (0, 2), (1, 2), (0, 3)])
        result = maximum_matching(g)
        self.assertEqual(result["mate"], [3, 2, 1, 0])
        self.assertGreaterEqual(result["blossom_contractions"], 1)

    def assert_raw_support_answer(self, groups, rhs):
        check = next((choices for choices in itertools.product(*groups)
                      if reduce(xor, choices, 0) == rhs), None)
        result = decide_unit_supports(groups, rhs)
        self.assertEqual(result["status"], "UNSAT" if check is None else "SAT", (groups, rhs))
        if check is None:
            self.assertIsNone(result["witness"])
            self.assertLess(2*result["matching_edges"], result["graph_vertices"])
        else:
            w = result["witness"]
            self.assertEqual(len(w), len(groups))
            self.assertTrue(all(x in g for x, g in zip(w, groups)))
            self.assertEqual(reduce(xor, w, 0), rhs)
            instance = reduce_unit_supports(groups, rhs)
            self.assertEqual(project_unit_matching(instance, lift_unit_choices(instance, check)), check)

    def test_all_supports_through_three_groups_two_rows(self):
        subsets = [tuple(x for j, x in enumerate((0, 1, 2)) if mask >> j & 1)
                   for mask in range(8)]
        for n in range(4):
            for groups in itertools.product(subsets, repeat=n):
                for rhs in range(4):
                    self.assert_raw_support_answer(groups, rhs)

    def test_random_signed_parities_and_larger_choice_sets(self):
        rng = random.Random(11831)
        for _ in range(200):
            d, n = rng.randrange(1, 7), rng.randrange(0, 8)
            values = [0] + [1 << i for i in range(d)]
            groups = [tuple(rng.choices(values, k=rng.randrange(1, 5))) for _ in range(n)]
            self.assert_raw_support_answer(groups, rng.randrange(1 << d))

    def test_absent_and_sparse_coordinates_and_no_zero_choices(self):
        high = 1 << 1224
        for groups, rhs in (((), 0), ((), high), (((0,),), high),
                            (((high,), (high,)), 0), (((high, 1), (high,)), high ^ 1),
                            (((1, 2), (1, 2), (1, 2)), 0), (((0,), (0,)), 0),
                            (((1, 1, 0), (2, 2)), 2)):
            self.assert_raw_support_answer(groups, rhs)

    def test_every_solution_lifts_and_every_perfect_matching_projects(self):
        groups, rhs = ((0, 1, 2), (0, 2), (0, 1)), 1
        graph = reduce_unit_supports(groups, rhs)
        models = {x for x in itertools.product(*groups) if reduce(xor, x, 0) == rhs}
        projections = set()
        mate = [-1] * len(graph.neighbors)
        def visit():
            if -1 not in mate:
                projections.add(project_unit_matching(graph, mate))
                return
            v = mate.index(-1)
            for w in graph.neighbors[v]:
                if mate[w] < 0:
                    mate[v], mate[w] = w, v
                    visit()
                    mate[v] = mate[w] = -1
        visit()
        self.assertEqual(models, projections)
        for x in models:
            self.assertEqual(project_unit_matching(graph, lift_unit_choices(graph, x)), x)

    def test_invalid_graph_and_input_and_witness(self):
        for gs, rhs in (([[], [3]], 0), ([[True]], 0), ([[-1]], 0), ([[1]], True),
                        ([[1]], -1), ([b''], 0), ('', 0)):
            with self.assertRaises(ValueError):
                reduce_unit_supports(gs, rhs)
        for g in ([[0]], [[1], []], [[], [2]], [[True], [0]]):
            with self.assertRaises(ValueError):
                maximum_matching(g)
        graph = reduce_unit_supports([[0, 1], [1, 2]], 3)
        for bad in ([0, 1], [], [True, 2]):
            with self.assertRaises(ValueError):
                lift_unit_choices(graph, bad)
        with self.assertRaises(ValueError):
            project_unit_matching(graph, [-1]*len(graph.neighbors))


if __name__ == "__main__":
    unittest.main()
