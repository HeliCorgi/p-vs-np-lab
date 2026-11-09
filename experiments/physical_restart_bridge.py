#!/usr/bin/env python3
"""Falsify polynomial success of uniform global restarts at zero temperature.

Model: E counts false clauses. A run starts from independent uniform bits and
changes one bit at a time, never increasing E. The exact-probability statement
for the disconnected family additionally uses the existing lazy, uniformly
selected-coordinate Metropolis kernel. Probabilities assume ideal fair bits;
seeded Python traces below are reproducibility controls only.

DISCONNECTED FAMILY, b>=1. Each three-variable block has all six pairwise
equality clauses and (x OR y OR z). The seven clauses are distinct, have width
two or three, and each variable occurs five times. Energy at weight k=0,1,2,3
is respectively 1,2,2,0. Both endpoints are absorbing. The probability h_k of
eventually reaching 111 solves 3*h_1=2*h_2, 3*h_2=1+2*h_1, hence
h=(0,2/5,3/5,1). Lazy steps cancel from these equations. Every mixed state has
a positive-probability path to an endpoint; a finite chain therefore reaches
an endpoint almost surely. For b blocks, H=product_i h_(k_i) is harmonic:
each step updates at most one factor, whose conditional expectation is itself.
All blocks reach endpoints almost surely (equivalently use independent local
clocks). On the absorbing states H is one only at the unique full solution.
Thus H is the full success probability, and its uniform-start average is
(sum_k choose(3,k)*h_k / 8)^b = 2^(-b). Any finite cutoff only decreases it.
K fresh attempts have success at most min(1,K*2^(-b)); running each attempt
to absorption gives exactly 1-(1-2^(-b))^K, and mean 2^b attempts.

CONNECTED FAMILY, b>=1. In each four-variable block (a,c,e,d), put the twelve
pairwise equality clauses and (a OR c OR e). Connect consecutive blocks by
(d_i OR d_(i+1)). There are N=4b variables, 14b-1 distinct clauses, widths
two or three, no unit clauses, and maximum occurrence at most eight. The
variable-clause incidence graph is connected. Equalities and positive triples
force the unique solution 1^N. A block initially 0000 can never change under
ANY one-bit update that does not increase E, independently of outside states:
flipping a,c,e creates three equality violations and removes one triple
violation, so Delta E=2; flipping d creates three equality violations and
removes at most two connector violations, so Delta E>=1. By induction this
block stays zero throughout the run. Each uniform initial block is zero with
probability 1/16, independently. Consequently

    Pr(success in one run) <= (15/16)^b,
    Pr(success in at most K fresh global runs) <= min(1,K*(15/16)^b).

The second bound even allows adaptive update order and adaptive stopping of
attempts. It only requires conditionally fresh uniform initial bits and a
fixed upper bound K on attempts. No finite run duration can repair it. With
standard binary variable indices the encoding length is O(b log b), so every
polynomial total-work budget, including initialization, still has success
tending to zero. Component-wise restarts alone do not remove the connected
example. Both families themselves are EASY: all ones is a checked witness.

Conditional bridge to complexity: a uniform, polynomial worst-case bit-cost
algorithm that outputs only verified witnesses and succeeds with probability
>=2/3 on EVERY satisfiable CNF puts SAT in RP, hence NP=RP. This alone does not
prove P=NP. A uniformly constructible polynomial list of polynomial-length
random tapes covering success for every satisfiable input would additionally
give deterministic polynomial SAT, hence P=NP. Neither premise is established
here. The bounds above refute the success premise for this global-reset,
zero-temperature rule. They say nothing prohibitive about preprocessing,
local resets, collective moves, positive/changing temperatures, quantum
algorithms, or all SAT algorithms. This is an elementary Markov-chain and
frozen-block argument, not a novelty claim, Lean proof, or P versus NP result.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json
from math import prod
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT))
from experiments.physical_sat import exact
from pnp_lab.physical_sat import chain, energy, restart_sample
from pnp_lab.sat_scaling import satisfies


def block_cnf(blocks, *, connected=False):
    """Construct the explicit easy counterexample; no assignment enumeration."""
    if type(blocks) is not int or blocks < 1:
        raise ValueError('positive integer block count required')
    width = 4 if connected else 3
    clauses = []
    for i in range(blocks):
        variables = tuple(range(width*i+1, width*(i+1)+1))
        for u, v in combinations(variables, 2):
            clauses.extend(((-u, v), (u, -v)))
        clauses.append(variables[:3])
    if connected:
        clauses.extend((4*i, 4*(i+1)) for i in range(1, blocks))
    return width*blocks, tuple(clauses)


def structure(n, clauses):
    """Check sizes and connectivity without using the block construction."""
    occurrences = Counter(abs(lit) for clause in clauses for lit in clause)
    neighbors = {v: set() for v in range(1, n+1)}
    for clause in clauses:
        scope = {abs(lit) for lit in clause}
        for v in scope:
            neighbors[v].update(scope-{v})
    unseen, components = set(neighbors), 0
    while unseen:
        pending = [unseen.pop()]
        components += 1
        while pending:
            fresh = neighbors[pending.pop()] & unseen
            unseen.difference_update(fresh)
            pending.extend(fresh)
    return dict(variables=n, clauses=len(clauses), components=components,
                maximum_occurrence=max(occurrences.values()),
                widths=sorted({len(c) for c in clauses}),
                distinct_clauses=len({frozenset(c) for c in clauses}) == len(clauses),
                all_ones_witness_checked=satisfies(clauses, (1 << n)-1))


def absorption_probabilities(rows, target):
    """Budgeted exact finite oracle: solve (I-Q)h=r, not a Monte Carlo estimate."""
    if not 0 <= target < len(rows) or len(rows) > 64:
        raise ValueError('target in a kernel of at most 64 states required')
    reachable = {target}
    while True:
        following = reachable | {i for i, row in enumerate(rows)
                                 if any(p and j in reachable for j, p in row.items())}
        if following == reachable:
            break
        reachable = following
    transient = sorted(reachable-{target})
    matrix = [[F(i == j)-rows[word].get(other, 0)
               for j, other in enumerate(transient)]+[rows[word].get(target, F(0))]
              for i, word in enumerate(transient)]
    for col in range(len(matrix)):
        pivot = next(row for row in range(col, len(matrix)) if matrix[row][col])
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scale = matrix[col][col]
        matrix[col] = [x/scale for x in matrix[col]]
        for row in range(len(matrix)):
            if row != col and matrix[row][col]:
                scale = matrix[row][col]
                matrix[row] = [x-scale*y for x, y in zip(matrix[row], matrix[col])]
    result = [F(0)]*len(rows)
    result[target] = F(1)
    for word, row in zip(transient, matrix):
        result[word] = row[-1]
    return result


def restart_bound(blocks, attempts, *, connected=False):
    if type(blocks) is not int or blocks < 1 or type(attempts) is not int or attempts < 0:
        raise ValueError('positive integer blocks and nonnegative integer attempts required')
    per_attempt = F(15, 16)**blocks if connected else F(1, 2)**blocks
    return per_attempt, min(F(1), attempts*per_attempt)


def audit():
    disjoint = []
    local_h = (F(0), F(2, 5), F(3, 5), F(1))
    for blocks in (1, 2):
        n, clauses = block_cnf(blocks)
        energies, rows = chain(n, clauses, 0)
        probabilities = absorption_probabilities(rows, (1 << n)-1)
        for word, probability in enumerate(probabilities):
            predicted = prod(local_h[((word >> (3*i)) & 7).bit_count()]
                             for i in range(blocks))
            if probability != predicted:
                raise AssertionError('full-kernel oracle refuted product absorption formula')
        mean = sum(probabilities)/len(rows)
        if mean != F(1, 2)**blocks or [w for w, e in enumerate(energies) if e == 0] != [(1 << n)-1]:
            raise AssertionError('basin probability or unique witness failed')
        disjoint.append(dict(blocks=blocks, **structure(n, clauses), states=len(rows),
                             eventual_uniform_success=exact(mean),
                             state_success_probabilities=[exact(p) for p in probabilities]))

    frozen = []
    for blocks in (1, 2, 3):
        n, clauses = block_cnf(blocks, connected=True)
        checked, minimum_delta, models, frozen_starts = 0, None, [], 0
        for word in range(1 << n):
            value = energy(clauses, word)
            if value == 0:
                models.append(word)
            has_frozen_block = False
            for i in range(blocks):
                if (word >> (4*i)) & 15:
                    continue
                has_frozen_block = True
                for j in range(4*i, 4*i+4):
                    delta = energy(clauses, word ^ (1 << j))-value
                    if delta <= 0:
                        raise AssertionError('zero block has a nonincreasing escape')
                    minimum_delta = delta if minimum_delta is None else min(minimum_delta, delta)
                    checked += 1
            frozen_starts += has_frozen_block
        if models != [(1 << n)-1] or (1 << n)-frozen_starts != 15**blocks:
            raise AssertionError('connected witness or independent initial-block count failed')
        info = structure(n, clauses)
        if (info['components'] != 1 or not info['distinct_clauses'] or
                info['maximum_occurrence'] > 8 or info['widths'] != [2, 3]):
            raise AssertionError('connected structural claim failed')
        frozen.append(dict(blocks=blocks, **info, assignments=1 << n,
                           frozen_block_flips_checked=checked, minimum_delta=minimum_delta,
                           initial_states_without_zero_block=15**blocks))

    trajectories = []
    for connected in (False, True):
        for blocks in (1, 4, 16):
            n, clauses = block_cnf(blocks, connected=connected)
            for seed in range(4):
                answer = restart_sample(n, clauses, seed=seed, max_attempts=8,
                                        ticks_per_attempt=1000)
                if answer['status'] not in ('SAT', 'UNKNOWN'):
                    raise AssertionError('search budget was converted to UNSAT')
                if answer['status'] == 'SAT' and not satisfies(clauses, answer['witness']):
                    raise AssertionError('invalid witness')
                if connected:
                    for attempt in answer['attempts']:
                        initial, final = attempt['initial_word'], attempt['result']['final_word']
                        for i in range(blocks):
                            if not ((initial >> (4*i)) & 15) and ((final >> (4*i)) & 15):
                                raise AssertionError('actual sampler escaped a frozen zero block')
                trajectories.append(dict(connected=connected, blocks=blocks, seed=seed, result=answer))

    evaluated_bounds = []
    for connected in (False, True):
        for blocks in (16, 128, 1024):
            n = (4 if connected else 3)*blocks
            per_attempt, overall = restart_bound(blocks, n**3, connected=connected)
            evaluated_bounds.append(dict(connected=connected, blocks=blocks, variables=n,
                                          attempt_budget=n**3,
                                          per_attempt_success_upper_bound=exact(per_attempt),
                                          overall_success_upper_bound=exact(overall)))
    return dict(all_checks_passed=True, disjoint_exact_kernels=disjoint,
                connected_frozen_checks=frozen, bounded_restart_runs=trajectories,
                evaluated_all_size_bounds=evaluated_bounds,
                stopped_branch='Polynomial success from uniform global resets of zero-temperature one-bit search.',
                complexity_bridge='Verified polynomial bounded-time success on every satisfiable input would give NP=RP; an effective polynomial deterministic covering of successful random tapes would give P=NP. Neither premise is obtained.',
                remaining_core='A different mechanism with a proved polynomial total-cost and success bound for every satisfiable input, including these families.',
                scope='All-size elementary proofs in the module docstring plus finite exact checks; no novelty, Lean formalization, hardware timing, general physical impossibility, or P versus NP separation claim.',
                polynomial_general_sat_algorithm=False, p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=ROOT / 'results')
    args = parser.parse_args()
    report = audit()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / 'physical_restart_bridge.json').write_text(
        json.dumps(report, sort_keys=True, indent=2)+'\n')
    print(json.dumps({key: report[key] for key in ('all_checks_passed', 'stopped_branch')}))


if __name__ == '__main__':
    main()
