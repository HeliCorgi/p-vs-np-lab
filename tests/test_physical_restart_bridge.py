from fractions import Fraction as F
from itertools import product
import unittest

from experiments.physical_restart_bridge import (
    absorption_probabilities, block_cnf, restart_bound, structure,
)
from pnp_lab.physical_sat import chain, restart_sample


def independent_energy(clauses, bits):
    return sum(all(bits[abs(lit)-1] != (lit > 0) for lit in clause) for clause in clauses)


class PhysicalRestartBridgeTests(unittest.TestCase):
    def test_distinct_bounded_occurrence_and_connectivity(self):
        for blocks in (1, 2, 3, 16):
            for connected in (False, True):
                n, clauses = block_cnf(blocks, connected=connected)
                info = structure(n, clauses)
                self.assertEqual(n, (4 if connected else 3)*blocks)
                self.assertEqual(len(clauses), 14*blocks-1 if connected else 7*blocks)
                self.assertTrue(info['distinct_clauses'])
                self.assertTrue(info['all_ones_witness_checked'])
                self.assertEqual(info['widths'], [2, 3])
                self.assertEqual(info['components'], 1 if connected else blocks)
                self.assertLessEqual(info['maximum_occurrence'], 8 if connected else 5)
        self.assertEqual(structure(*block_cnf(3, connected=True))['maximum_occurrence'], 8)

    def test_independent_energy_and_unique_model(self):
        for blocks in (1, 2):
            for connected in (False, True):
                n, clauses = block_cnf(blocks, connected=connected)
                models = [bits for bits in product((False, True), repeat=n)
                          if independent_energy(clauses, bits) == 0]
                self.assertEqual(models, [(True,)*n])
        _, clauses = block_cnf(1)
        for bits in product((False, True), repeat=3):
            self.assertEqual(independent_energy(clauses, bits), (1, 2, 2, 0)[sum(bits)])

    def test_exact_absorption_oracle_and_product_identity(self):
        h = (F(0), F(2, 5), F(3, 5), F(1))
        for blocks in (1, 2):
            _, rows = chain(*block_cnf(blocks), 0)
            probabilities = absorption_probabilities(rows, len(rows)-1)
            for word, probability in enumerate(probabilities):
                expected = F(1)
                for i in range(blocks):
                    expected *= h[((word >> (3*i)) & 7).bit_count()]
                self.assertEqual(probability, expected)
                self.assertEqual(sum(p*probabilities[j] for j, p in rows[word].items()), probability)
            self.assertEqual(sum(probabilities)/len(rows), F(1, 2)**blocks)
        # A separate kernel with a non-target closed class checks zero boundary
        # values and a geometric self-loop, not just the SAT-generated matrices.
        kernel = [{0: F(1)}, {0: F(1, 4), 1: F(1, 2), 2: F(1, 4)}, {2: F(1)}]
        self.assertEqual(absorption_probabilities(kernel, 2), [F(0), F(1, 2), F(1)])

    def test_finite_deadlines_cannot_exceed_eventual_basin(self):
        _, rows = chain(*block_cnf(2), 0)
        distribution = [F(1, len(rows))]*len(rows)
        previous = F(0)
        for _ in range(40):
            self.assertLessEqual(previous, distribution[-1])
            self.assertLessEqual(distribution[-1], F(1, 4))
            previous = distribution[-1]
            following = [F(0)]*len(rows)
            for word, mass in enumerate(distribution):
                for target, probability in rows[word].items():
                    following[target] += mass*probability
            distribution = following
        self.assertGreater(distribution[-1], F(1, 5))

    def test_frozen_block_for_every_outside_assignment(self):
        for blocks in (1, 2, 3):
            n, clauses = block_cnf(blocks, connected=True)
            for i in range(blocks):
                outside = [j for j in range(n) if j//4 != i]
                for values in product((False, True), repeat=len(outside)):
                    bits = [False]*n
                    for j, value in zip(outside, values):
                        bits[j] = value
                    before = independent_energy(clauses, bits)
                    for j in range(4*i, 4*i+4):
                        following = list(bits)
                        following[j] = True
                        delta = independent_energy(clauses, following)-before
                        self.assertGreaterEqual(delta, 1 if j % 4 == 3 else 2)

    def test_bound_counts_costs_and_is_not_an_all_dynamics_claim(self):
        for blocks in (1, 2, 3):
            no_zero_blocks = sum(all(any(bits[4*i:4*i+4]) for i in range(blocks))
                                 for bits in product((False, True), repeat=4*blocks))
            p, bound = restart_bound(blocks, 2, connected=True)
            self.assertEqual(p, F(no_zero_blocks, 2**(4*blocks)))
            self.assertEqual(bound, min(F(1), 2*p))
        self.assertEqual(restart_bound(3, 0)[1], 0)
        self.assertLess(restart_bound(1024, 4096**3, connected=True)[1], F(1, 10**17))
        n, clauses = block_cnf(1, connected=True)
        _, positive_temperature = chain(n, clauses, F(1, 2))
        self.assertGreater(sum(p for j, p in positive_temperature[0].items() if j), 0)
        self.assertLess(independent_energy(clauses, [True]*n), independent_energy(clauses, [False]*n))

    def test_actual_restarts_preserve_blocks_and_charge_initialization(self):
        n, clauses = block_cnf(8, connected=True)
        for seed in range(3):
            answer = restart_sample(n, clauses, seed=seed, max_attempts=3, ticks_per_attempt=300)
            self.assertIn(answer['status'], ('SAT', 'UNKNOWN'))
            for attempt in answer['attempts']:
                initial, final = attempt['initial_word'], attempt['result']['final_word']
                for i in range(8):
                    if not ((initial >> (4*i)) & 15):
                        self.assertEqual((final >> (4*i)) & 15, 0)
            if answer['status'] == 'SAT':
                self.assertEqual(answer['witness'], (1 << n)-1)
            self.assertEqual(answer['initialization_bit_writes'], n*len(answer['attempts']))
            self.assertEqual(answer['initialization_random_bits'], (n+64)*len(answer['attempts']))
            self.assertEqual(answer['random_bits'], answer['initialization_random_bits']+
                             sum(a['result']['random_bits'] for a in answer['attempts']))

    def test_invalid_sizes_and_finite_oracle_budget(self):
        for blocks in (True, 0, -1, 1.5):
            with self.assertRaises(ValueError):
                block_cnf(blocks)
            with self.assertRaises(ValueError):
                restart_bound(blocks, 2)
        for attempts in (True, -1, 1.5):
            with self.assertRaises(ValueError):
                restart_bound(1, attempts)
        with self.assertRaises(ValueError):
            absorption_probabilities([{i: F(1)} for i in range(65)], 64)


if __name__ == '__main__':
    unittest.main()
