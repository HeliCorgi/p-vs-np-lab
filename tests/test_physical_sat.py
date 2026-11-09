from fractions import Fraction as F
from itertools import product
import json
from math import comb
import random
import unittest

from experiments.physical_sat import exact, log2_floor
from pnp_lab.physical_sat import (
    PhysicalBudgetExceeded, acceptance, chain, deadline_bound, energy, mean_hitting,
    restart_sample, sample, spin_polynomial, spin_value, trap_cnf, trap_energy, trap_rates,
    trap_summary, zero_temperature_restart_control,
)


def literal_energy(clauses, bits):
    return sum(not any(bits[abs(lit)-1] == (lit > 0) for lit in c) for c in clauses)


def weight_hit_probability(n, rho, ticks):
    up, down = trap_rates(n, rho)
    distribution = [F(1)]+[F(0)]*n
    for _ in range(ticks):
        following = [F(0)]*(n+1)
        following[n] = distribution[n]
        for k, mass in enumerate(distribution[:-1]):
            following[k] += mass*(1-up[k]-down[k])
            following[k+1] += mass*up[k]
            if k:
                following[k-1] += mass*down[k]
        distribution = following
    return distribution[n]


class PhysicalSATTests(unittest.TestCase):
    def test_every_three_variable_proper_cnf_spin_encoding(self):
        universe = list(product((1, -1), (2, -2), (3, -3)))
        for mask in range(256):
            clauses = [c for j, c in enumerate(universe) if mask & (1 << j)]
            polynomial = spin_polynomial(3, clauses)
            self.assertTrue(all(m.bit_count() <= 3 and 8 % c.denominator == 0 for m, c in polynomial.items()))
            for bits in product((False, True), repeat=3):
                word = sum(int(bit) << j for j, bit in enumerate(bits))
                self.assertEqual(spin_value(polynomial, word), literal_energy(clauses, bits))

    def test_mixed_width_empty_duplicate_and_unused_variables(self):
        rng = random.Random(91121)
        cases = [(0, []), (0, [()]), (3, [(1,), (1,), (-1, 2), ()])]
        for n in range(1, 7):
            for _ in range(8):
                clauses = [tuple(v if rng.randrange(2) else -v for v in
                                 rng.sample(range(1, n+1), rng.randrange(min(3, n)+1)))
                           for _ in range(rng.randrange(8))]
                cases.append((n, clauses))
        for n, clauses in cases:
            polynomial = spin_polynomial(n, clauses)
            for bits in product((False, True), repeat=n):
                word = sum(int(bit) << j for j, bit in enumerate(bits))
                expected = literal_energy(clauses, bits)
                self.assertEqual(energy(clauses, word), expected)
                self.assertEqual(spin_value(polynomial, word), expected)

    def test_trap_family_energy_and_bounded_ising_couplings(self):
        for n in range(2, 9):
            clauses = trap_cnf(n)
            self.assertEqual(len(clauses), 2*n*n-n)
            expected = {0: F(n*n, 2)}
            expected.update({1 << j: F(-1, 2) for j in range(n)})
            expected.update({(1 << i) | (1 << j): F(-1) for i in range(n) for j in range(i+1, n)})
            self.assertEqual(spin_polynomial(n, clauses), expected)
            for word in range(1 << n):
                self.assertEqual(energy(clauses, word), trap_energy(n, word.bit_count()))
            self.assertEqual([word for word in range(1 << n) if energy(clauses, word) == 0], [(1 << n)-1])

    def test_kernel_stochasticity_balance_and_infinite_temperature(self):
        clauses = ((1, -2, 3), (-1, 2), (1,))
        for rho in (F(1, 7), F(1, 2), F(1)):
            energies, rows = chain(3, clauses, rho)
            weights = [rho**e for e in energies]
            for i, row in enumerate(rows):
                self.assertEqual(sum(row.values()), 1)
                self.assertGreaterEqual(row[i], F(1, 2))
                for j, probability in row.items():
                    self.assertGreaterEqual(probability, 0)
                    self.assertEqual(weights[i]*probability, weights[j]*rows[j].get(i, 0))
                    if rho == 1:
                        self.assertEqual(probability, F(1, 2) if i == j else F(1, 6))

    def test_exact_hitting_handles_targets_absence_and_closed_traps(self):
        for rho in (F(0), F(1, 2), F(1)):
            _, rows = chain(1, ((1,),), rho)
            self.assertEqual(mean_hitting(rows, [1], 0), 2)
            self.assertEqual(mean_hitting(rows, [1], 1), 0)
            self.assertIsNone(mean_hitting(rows, [], 0))
        _, rows = chain(2, trap_cnf(2), F(0))
        self.assertIsNone(mean_hitting(rows, [3], 0))
        # Half the mass reaches a target; half enters a closed non-target class.
        kernel = [{1: F(1, 2), 2: F(1, 2)}, {1: F(1)}, {2: F(1)}]
        self.assertIsNone(mean_hitting(kernel, [1], 0))

    def test_birth_death_recurrence_against_full_assignment_kernel(self):
        for n in (2, 3, 4, 5):
            for rho in (F(1, 4), F(3, 4), F(1)):
                _, rows = chain(n, trap_cnf(n), rho)
                result = trap_summary(n, rho)
                self.assertEqual(mean_hitting(rows, [(1 << n)-1], 0), result['mean_ticks'])
                up, down = trap_rates(n, rho)
                for word, row in enumerate(rows):
                    k = word.bit_count()
                    self.assertEqual(sum(p for j, p in row.items() if j.bit_count() == k+1), up[k])
                    self.assertEqual(sum(p for j, p in row.items() if j.bit_count() == k-1), down[k])
        for n in (2, 4, 8, 16, 32):
            r = trap_summary(n, F(1, 2))
            self.assertEqual(r['first_exit_mean_ticks'], 2**(2*n-2))
            self.assertGreaterEqual(r['stationary_ground_probability'], 1/(1+F(3, 4)**n-F(1, 4)**n))

    def test_deadline_bounds_and_warm_domination_obligation(self):
        for n in (16, 32):
            for rho in (F(1, 4), F(1, 2)):
                probability = weight_hit_probability(n, rho, 2*n)
                bound = deadline_bound(n, 2*n, rho)['probability_upper_bound']
                self.assertLess(bound, 1)
                self.assertLessEqual(probability, bound)
        for n in (2, 4, 8, 16, 32, 64):
            for rho in (F(n-1, n), F(1)):
                self.assertGreaterEqual(rho**n, F(1, 8))
                for k in range(n+1):
                    if k < n:
                        p_one = acceptance(rho, trap_energy(n, k+1)-trap_energy(n, k))/2
                        self.assertLessEqual(p_one, F(127, 128))
                    if k:
                        p_one = 1-acceptance(rho, trap_energy(n, k-1)-trap_energy(n, k))/2
                        self.assertLessEqual(p_one, F(127, 128))
        self.assertEqual(deadline_bound(16, 10**6, F(0))['probability_upper_bound'], 0)
        self.assertLess(deadline_bound(8192, 8192**3)['probability_upper_bound'], F(1, 10**16))

    def test_uniform_initialization_control_by_absorbing_dag(self):
        for n in (2, 4, 6):
            energies, rows = chain(n, trap_cnf(n), F(0))
            probability, duration = {0: F(0), (1 << n)-1: F(1)}, {0: F(0), (1 << n)-1: F(0)}
            for word in sorted(range(1 << n), key=energies.__getitem__):
                if word in probability:
                    continue
                exits = {j: p for j, p in rows[word].items() if j != word and p}
                self.assertTrue(all(energies[j] < energies[word] for j in exits))
                denominator = sum(exits.values())
                probability[word] = sum(p*probability[j] for j, p in exits.items())/denominator
                duration[word] = (1+sum(p*duration[j] for j, p in exits.items()))/denominator
            control = zero_temperature_restart_control(n)
            self.assertEqual(sum(probability.values())/(1 << n), F(1, 2))
            self.assertEqual(sum(duration.values())/(1 << n), control['mean_ticks_to_either_endpoint'])
            self.assertEqual(control['mean_ticks_until_success_with_endpoint_restarts'], 2*sum(duration.values())/(1 << n))

    def test_sampler_returns_checked_witness_or_unknown_never_timeout_unsat(self):
        for seed in range(12):
            for n, clauses in ((0, []), (0, [()]), (1, [(1,), (-1,)]),
                               (3, [(1,), (2,), (3,)]), (4, trap_cnf(4))):
                answer = sample(n, clauses, seed=seed, max_ticks=50)
                self.assertIn(answer['status'], ('SAT', 'UNKNOWN'))
                if answer['status'] == 'SAT':
                    bits = tuple(bool(answer['witness'] & (1 << j)) for j in range(n))
                    self.assertEqual(literal_energy(clauses, bits), 0)
                else:
                    self.assertIsNone(answer['witness'])
        self.assertEqual(sample(3, [(1,)], initial=1, max_ticks=0)['status'], 'SAT')
        self.assertEqual(sample(3, [(1,)], max_ticks=0)['status'], 'UNKNOWN')

    def test_sampler_precision_and_randomness_budgets(self):
        answer = sample(3, [(1,)], max_random_bits=0)
        self.assertEqual((answer['status'], answer['reason']), ('UNKNOWN', 'random_bit_budget'))
        answer = sample(4, trap_cnf(4), max_probability_bits=0, seed=0)
        self.assertEqual((answer['status'], answer['reason']), ('UNKNOWN', 'probability_bit_budget'))
        self.assertGreater(acceptance(F(1, 2), 2000), 0)
        self.assertEqual(acceptance(F(1, 2), 2000).denominator, 1 << 2000)
        a = sample(4, trap_cnf(4), seed=3, max_ticks=100)
        self.assertEqual(a, sample(4, trap_cnf(4), seed=3, max_ticks=100))
        self.assertLessEqual(a['random_bits'], 1_000_000)

    def test_restarts_charge_preparation_and_preserve_unknown(self):
        n, clauses = 8, trap_cnf(8)
        answer = restart_sample(n, clauses, seed=0, max_attempts=8)
        self.assertEqual(answer['status'], 'SAT')
        self.assertEqual(energy(clauses, answer['witness']), 0)
        self.assertEqual(answer['initialization_bit_writes'], n*len(answer['attempts']))
        self.assertEqual(answer['random_bits'], answer['initialization_random_bits']+
                         sum(a['result']['random_bits'] for a in answer['attempts']))
        self.assertEqual(answer['literal_inspections'], sum(a['result']['literal_inspections'] for a in answer['attempts']))
        self.assertLessEqual(answer['ticks'], 8000)
        self.assertEqual(restart_sample(1, [(1,), (-1,)], max_attempts=2, ticks_per_attempt=20)['status'], 'UNKNOWN')
        limited = restart_sample(n, clauses, max_random_bits=n+63)
        self.assertEqual((limited['status'], limited['reason'], limited['attempts']), ('UNKNOWN', 'random_bit_budget', []))
        self.assertEqual(sample(n, clauses, rho=0, stop_at_local_minimum=True)['reason'], 'strict_local_minimum')

    def test_bad_inputs_and_reference_state_budget(self):
        for n, clauses in ((-1, []), (1, [(0,)]), (1, [(1, -1)]), (4, [(1, 2, 3, 4)])):
            with self.assertRaises(ValueError):
                spin_polynomial(n, clauses)
        for rho in (True, -1, F(3, 2), 0.5):
            with self.assertRaises(ValueError):
                sample(1, [(1,)], rho=rho)
        with self.assertRaises(ValueError):
            sample(1, [], initial=2)
        with self.assertRaises(PhysicalBudgetExceeded):
            chain(6, [], F(1), max_states=63)
        self.assertEqual(len(chain(5, [], F(1), max_states=32)[0]), 32)
        with self.assertRaises(ValueError):
            deadline_bound(3, 100)
        with self.assertRaises(ValueError):
            zero_temperature_restart_control(3)

    def test_large_exact_probabilities_survive_serialization(self):
        for value in (F(0), F(1), F(127, 128)**8192, F(2)**20000):
            record = json.loads(json.dumps(exact(value)))
            restored = F(int(record['numerator_hex'], 16), int(record['denominator_hex'], 16))
            self.assertEqual(restored, value)
        for exponent in (-1000, -1, 0, 1, 1000):
            self.assertEqual(log2_floor(F(2)**exponent), exponent)
            self.assertEqual(log2_floor(F(3, 4)*F(2)**exponent), exponent-1)


if __name__ == '__main__':
    unittest.main()
