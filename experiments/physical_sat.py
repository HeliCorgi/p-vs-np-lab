#!/usr/bin/env python3
"""Exact controls and bounded trajectories for the SAT spin-dynamics proposal."""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
import json
from math import comb
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'src'))
from pnp_lab.physical_sat import (chain, deadline_bound, energy, mean_hitting,
    restart_sample, sample, spin_polynomial, spin_value, trap_cnf, trap_energy, trap_rates,
    trap_summary, zero_temperature_restart_control)
from pnp_lab.sat_scaling import satisfies


def log2_floor(value):
    value = F(value)
    if value <= 0:
        raise ValueError('positive value required')
    candidate = value.numerator.bit_length()-value.denominator.bit_length()
    return candidate if value >= F(2)**candidate else candidate-1


def exact(value):
    value = F(value)
    # Hex keeps large exact probabilities portable without disabling Python's
    # decimal-string size limit. The decimal field is explicitly approximate.
    with localcontext() as context:
        context.prec = 8
        approximate = format(Decimal(value.numerator)/Decimal(value.denominator), '.6E')
    return dict(numerator_hex=hex(value.numerator), denominator_hex=hex(value.denominator),
                approximate_decimal=approximate,
                floor_log2=log2_floor(value) if value > 0 else None)


def audit():
    rng = random.Random(91103)
    formula_cases = [(0, ()), (0, ((),)), (1, ((1,), (-1,)))]
    for n in range(1, 7):
        for _ in range(8):
            clauses = []
            for _ in range(rng.randrange(1, 9)):
                scope = rng.sample(range(1, n+1), rng.randrange(min(3, n)+1))
                clauses.append(tuple(v if rng.randrange(2) else -v for v in scope))
            formula_cases.append((n, tuple(clauses)))
    checked_assignments = reference_states = 0
    polynomial_terms_peak = coupling_bits_peak = 0
    general_rows = []
    for n, clauses in formula_cases:
        polynomial = spin_polynomial(n, clauses)
        polynomial_terms_peak = max(polynomial_terms_peak, len(polynomial))
        for value in polynomial.values():
            coupling_bits_peak = max(coupling_bits_peak, abs(value.numerator).bit_length(), value.denominator.bit_length())
            if 8 % value.denominator:
                raise AssertionError('width-three spin precision bound failed')
        for word in range(1 << n):
            if spin_value(polynomial, word) != energy(clauses, word):
                raise AssertionError('spin polynomial does not preserve the original clause energy')
            checked_assignments += 1
        if n <= 4:
            energies, rows = chain(n, clauses, F(1, 2))
            invariant = [F(1, 2)**value for value in energies]
            for i, row in enumerate(rows):
                if sum(row.values()) != 1 or any(p < 0 for p in row.values()):
                    raise AssertionError('invalid Markov kernel')
                for j, p in row.items():
                    if invariant[i]*p != invariant[j]*rows[j].get(i, 0):
                        raise AssertionError('detailed balance failed')
            targets = [i for i, value in enumerate(energies) if value == 0]
            mean = mean_hitting(rows, targets, 0)
            if bool(targets) != (mean is not None):
                raise AssertionError('positive-temperature reachability mismatch')
            general_rows.append(dict(variables=n, clauses=clauses, model_count=len(targets),
                                     mean_ticks_from_zero=exact(mean) if mean is not None else None))
            reference_states += len(rows)
    orbit_checks = []
    for n in (2, 3, 4, 5):
        clauses = trap_cnf(n)
        for word in range(1 << n):
            if energy(clauses, word) != trap_energy(n, word.bit_count()):
                raise AssertionError('CNF-to-weight energy mismatch')
        for rho in (F(0), F(1, 4), F(1, 2), F(1)):
            energies, rows = chain(n, clauses, rho)
            up, down = trap_rates(n, rho)
            for word, row in enumerate(rows):
                k = word.bit_count()
                if (sum(p for j, p in row.items() if j.bit_count() == k+1) != up[k]
                        or sum(p for j, p in row.items() if j.bit_count() == k-1) != down[k]):
                    raise AssertionError('birth-death compression failed')
            expected = trap_summary(n, rho)['mean_ticks']
            measured = mean_hitting(rows, [len(rows)-1], 0)
            if expected != measured:
                raise AssertionError('exact hitting equations disagree with compressed recurrence')
            orbit_checks.append(dict(variables=n, rho=exact(rho), mean_ticks=exact(expected) if expected is not None else None))
            reference_states += len(rows)
    thermal = []
    for n in (2, 4, 8, 16, 32, 64, 128):
        temperatures = (F(1, 2), F(1)) if n >= 64 else tuple(sorted({F(1, 4), F(1, 2), F(3, 4), F(7, 8), F(n-1, n), F(1)}))
        for rho in temperatures:
            result = trap_summary(n, rho)
            if rho == F(1, 2):
                concentration = 1/(1+F(3, 4)**n-F(1, 4)**n)
                if result['stationary_ground_probability'] < concentration:
                    raise AssertionError('ground-state concentration inequality failed')
                if result['first_exit_mean_ticks'] != 2**(2*n-2):
                    raise AssertionError('first-exit clock bound failed')
            if rho == 1 and result['stationary_ground_probability'] != F(1, 1 << n):
                raise AssertionError('infinite-temperature control failed')
            thermal.append(dict(variables=n, clause_positions=2*n*n-n, rho=exact(rho),
                                mean_ticks=exact(result['mean_ticks']),
                                first_exit_mean_ticks=exact(result['first_exit_mean_ticks']),
                                stationary_ground_probability=exact(result['stationary_ground_probability']),
                                max_exit_rate_n_clock_mean_time=exact(result['mean_ticks']/n)))
    trajectories = []
    examples = [
        ('independent_units', 10, tuple((i,) for i in range(1, 11)), F(0), 0),
        ('ferromagnetic_trap', 10, trap_cnf(10), F(1, 2), 0),
        ('same_formula_ground_initialization', 10, trap_cnf(10), F(1, 2), (1 << 10)-1),
        ('contradictory_units', 1, ((1,), (-1,)), F(1, 2), 0),
    ]
    for name, n, clauses, rho, initial in examples:
        for seed in range(3):
            answer = sample(n, clauses, rho=rho, initial=initial, seed=seed, max_ticks=2000)
            if answer['status'] == 'SAT' and not satisfies(clauses, answer['witness']):
                raise AssertionError('returned SAT witness did not replay')
            if answer['status'] not in ('SAT', 'UNKNOWN'):
                raise AssertionError('bounded trajectory issued an unsupported UNSAT decision')
            trajectories.append(dict(case=name, variables=n, clauses=len(clauses), rho=exact(rho),
                                     seed=seed, initial_word=initial, result=answer))
    controls = []
    for n in (2, 4, 8, 16, 32, 64, 128):
        control = zero_temperature_restart_control(n)
        if control['success_probability_per_attempt'] != F(1, 2):
            raise AssertionError('uniform-start basin probability failed')
        controls.append(dict(variables=n, success_probability_per_attempt=exact(control['success_probability_per_attempt']),
                             mean_ticks_to_either_endpoint=exact(control['mean_ticks_to_either_endpoint']),
                             mean_ticks_until_success_with_endpoint_restarts=exact(control['mean_ticks_until_success_with_endpoint_restarts'])))
    restart_runs = []
    for n in (8, 16, 24):
        clauses = trap_cnf(n)
        for seed in range(4):
            answer = restart_sample(n, clauses, seed=seed)
            if answer['status'] == 'SAT' and not satisfies(clauses, answer['witness']):
                raise AssertionError('restart witness failed original-CNF verification')
            restart_runs.append(dict(variables=n, seed=seed, result=answer))
    unsat_restart = restart_sample(1, ((1,), (-1,)), seed=0, max_attempts=2, ticks_per_attempt=20)
    if unsat_restart['status'] != 'UNKNOWN':
        raise AssertionError('unsatisfiable bounded restart control must remain UNKNOWN')
    # These are evaluated consequences of the all-size proof, not trajectories
    # or exponentially large enumerations at these sizes.
    deadlines = [dict(variables=n, ticks=n**3,
                      probability_upper_bound=exact(deadline_bound(n, n**3)['probability_upper_bound']))
                 for n in (1024, 4096, 8192)]
    return dict(all_checks_passed=True, encoding_cases=len(formula_cases),
                encoding_assignments_checked=checked_assignments,
                spin_terms_peak=polynomial_terms_peak, coupling_bits_peak=coupling_bits_peak,
                general_kernel_cases=general_rows, orbit_checks=orbit_checks,
                reference_states_enumerated=reference_states, thermal_cases=thermal,
                trajectories=trajectories, restart_controls=controls, restart_runs=restart_runs,
                unsat_restart_control=unsat_restart, deadline_consequences=deadlines,
                model='Classical lazy single-spin Metropolis, rational rho=exp(-beta), one random-coordinate tick; finite trajectories never assert UNSAT.',
                all_size_bound='For even n>=2, initial 0^n and any fixed rho in [0,1]: Pr(hit 1^n by t) <= min(1,(t+1)*max(2^(2-n/2),(127/128)^n)). See module docstring proof.',
                cold_stationarity_bound='At rho=1/2, stationary ground probability >=1/(1+(3/4)^n-4^(-n)), while mean first exit >=2^(2n-2) ticks.',
                stopped_branch='Fixed-temperature, zero-initialized local Metropolis as a universal fast SAT solver.',
                remaining_core='A different dynamics/initialization/schedule must prove correctness and total resource bounds on all inputs, including certifiable UNSAT; this audit supplies no such mechanism.',
                easy_control_scope='All positive unit clauses explicitly give the solution; uniform initialization with zero-temperature endpoint restarts also solves this family in expected polynomial work.',
                randomness_scope='Exact kernels and theorems use ideal fair bits; seeded trajectories are deterministic reproducibility controls.',
                scope='Classical finite-state model and elementary analytic bounds, not real hardware timing, quantum computation, a Lean verification, a novel complexity result, or an all-algorithm lower bound.',
                polynomial_general_sat_algorithm=False, all_physical_methods_excluded=False, p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), indent=2, sort_keys=True)+'\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir/'physical_sat.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
