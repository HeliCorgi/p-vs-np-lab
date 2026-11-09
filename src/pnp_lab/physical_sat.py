"""SAT as local spin energy, with resource-bounded lazy Metropolis dynamics.

This is a classical stochastic model, not physical hardware or quantum dynamics.
E_F is the number of false clause POSITIONS. With x_i=(1+s_i)/2, each false
literal is (1-sign(literal)*s_i)/2, so width<=3 CNF gives an exact local spin
polynomial of degree<=3 with at most 8m contributions. Its coefficients have
denominator dividing 8. Zero energy is equivalent to satisfying the input CNF.

A clock tick chooses a variable uniformly, stays put with probability 1/2,
and otherwise accepts its flip with probability min(1,rho^DeltaE), where
rho=exp(-beta) in energy units of one false clause. The rational sampler uses
exact random-integer rejection, never floating-point underflow. Budget exhaustion
returns UNKNOWN, never UNSAT. Counts include null ticks, probability bit lengths,
literal work and generated random bits. A seed makes runs reproducible, not
independent physical evidence. The probabilistic theorems assume ideal fair bits.

Adversarial control (an EASY formula, not a hard SAT family): n positive unit
clauses, plus two copies of each of (!x_i OR x_j), (x_i OR !x_j), for i<j.
It has m=2n^2-n clauses, coefficients bounded by two in its pair penalties,
and unique solution 1^n. At Hamming weight k,

    E_n(k)=n-k+2*k*(n-k).

Permutation symmetry makes the weight a birth-death chain, with upward rate
a_k=(n-k)/(2n)*min(1,rho^(E(k+1)-E(k))) and analogous downward rate b_k.
For rho>0 its invariant weights are w_k=choose(n,k)*rho^E(k). The exact mean
first hitting time of n from 0 is sum_k d_k, where d_0=1/a_0 and
d_k=(1+b_k*d_(k-1))/a_k. This is derived from the hitting-time equations,
not an assumed equilibration oracle. At rho=1/2 the ground-state stationary
probability is at least 1/(1+(3/4)^n-4^(-n)), yet the first exit from 0 alone
takes mean 2^(2n-2) ticks. Equilibrium concentration does not bound relaxation.

ALL-SIZE DEADLINE BOUND, even n>=2, initial state 0^n, any FIXED rho in [0,1]:
Pr(hit 1^n by tick t) <= min(1,(t+1)*max(2^(2-n/2),(127/128)^n)).

Proof, cold case rho^n<=1/8: for rho>0 reversibility gives
P^s(0,n/2)<=w_(n/2)/w_0 <= 2^n*rho^(n(n-1)/2)
<=2^(3/2-n/2)<=2^(2-n/2). Every one-spin path to n visits n/2, so a union
bound proves the claim. For rho=0, 0^n is absorbing (n>=2).

Warm case rho^n>=1/8: every upward energy jump is <=2n-1. Thus every proposed
flip is accepted with probability >=rho^(2n-1)>=1/64. Conditional on selecting
one coordinate, its new probability of being 1 is <=1/2 if currently 0 and
<=1-1/128 if currently 1. Couple to a process that resets the selected coordinate
to an independent Bernoulli(127/128) bit, starting with all zeros and using the
same selection and uniform random number. It dominates each original bit.
Conditional on the selection schedule, its last reset values are independent;
its probability of being all ones is <=(127/128)^n. Union-bound over ticks.
Both bounds decay exponentially in n, so polynomially many ticks fail with
probability tending to one, uniformly over the fixed temperature choice.
This probability argument is needed: a large mean alone would not prove it.

Scope: the bound covers this initialization and local fixed-temperature rule,
including polynomial rescalings of the total clock rate. It does not cover
arbitrary physical solvers, changing temperatures, random initialization,
restarts from other states, collective updates, quantum algorithms or all SAT
algorithms. In fact, zero-temperature dynamics from a uniform initial state
reaches the solution basin with probability exactly 1/2 for even n. Its mean
time to reach either endpoint is O(n log n); restarting after the wrong
endpoint makes this family easy. The unit clauses also give a deterministic
polynomial solution. No complexity separation, general solver, Lean proof,
or novelty claim is made. These are finite-state Markov-chain arguments.
"""
from __future__ import annotations

from fractions import Fraction as F
from math import comb
import random

from .sat_scaling import satisfies, validate


class PhysicalBudgetExceeded(RuntimeError):
    pass


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f'{name} must be a nonnegative integer')


def _input(n, clauses):
    clauses = tuple(tuple(c) for c in clauses)
    validate(n, clauses)
    if any(len(c) > 3 for c in clauses):
        raise ValueError('width at most three required')
    return clauses


def _rho(rho):
    if type(rho) not in (int, F) or not 0 <= rho <= 1:
        raise ValueError('an exact rational rho in [0,1] is required')
    return F(rho)


def energy(clauses, word):
    return sum(not any(bool(word & (1 << (abs(lit)-1))) == (lit > 0) for lit in c)
               for c in clauses)


def spin_polynomial(n, clauses):
    """Exact coefficients indexed by subsets; spin i is +1 iff Boolean bit i=1."""
    clauses = _input(n, clauses)
    result = {}
    for clause in clauses:
        terms = {0: F(1)}
        for lit in clause:
            bit, sign = 1 << (abs(lit)-1), 1 if lit > 0 else -1
            following = {}
            for mask, value in terms.items():
                following[mask] = following.get(mask, F(0)) + value/2
                following[mask | bit] = following.get(mask | bit, F(0)) - sign*value/2
            terms = following
        for mask, value in terms.items():
            result[mask] = result.get(mask, F(0)) + value
    return {mask: value for mask, value in result.items() if value}


def spin_value(polynomial, word):
    return sum(value*(-1)**((mask & ~word).bit_count()) for mask, value in polynomial.items())


def acceptance(rho, delta):
    return F(1) if delta <= 0 else rho**delta


def sample(n, clauses, *, rho=F(1, 2), initial=0, seed=0, max_ticks=2000,
           max_random_bits=1_000_000, max_probability_bits=100_000,
           stop_at_local_minimum=False):
    """Witness search only. A bounded trajectory cannot establish UNSAT."""
    clauses, rho = _input(n, clauses), _rho(rho)
    for value, name in ((initial, 'initial word'), (max_ticks, 'tick budget'),
                        (max_random_bits, 'random-bit budget'),
                        (max_probability_bits, 'probability-bit budget')):
        _natural(value, name)
    if initial.bit_length() > n:
        raise ValueError('initial word exceeds the declared variables')
    if type(stop_at_local_minimum) is not bool or (stop_at_local_minimum and rho != 0):
        raise ValueError('strict local-minimum stopping is restricted to zero temperature')
    rng = random.Random(seed)
    stats = dict(ticks=0, flip_proposals=0, accepted_flips=0, random_bits=0,
                 random_integer_trials=0, literal_inspections=0, probability_bits_peak=0)

    def draw(stop):
        if stop == 1:
            return 0
        width = (stop-1).bit_length()
        while True:
            if stats['random_bits'] + width > max_random_bits:
                raise PhysicalBudgetExceeded('random_bit_budget')
            value = rng.getrandbits(width)
            stats['random_bits'] += width
            stats['random_integer_trials'] += 1
            if value < stop:
                return value

    def measure(word):
        value = 0
        for clause in clauses:
            for lit in clause:
                stats['literal_inspections'] += 1
                if bool(word & (1 << (abs(lit)-1))) == (lit > 0):
                    break
            else:
                value += 1
        return value

    word = initial
    current = measure(word)
    minimum = current
    reason = 'no_variables' if not n and current else 'tick_budget'
    changed = True
    try:
        while current and stats['ticks'] < max_ticks and n:
            if stop_at_local_minimum and changed:
                if all(measure(word ^ (1 << j)) > current for j in range(n)):
                    reason = 'strict_local_minimum'
                    break
                changed = False
            stats['ticks'] += 1
            variable = draw(n)
            if draw(2) == 0:
                continue
            stats['flip_proposals'] += 1
            following = word ^ (1 << variable)
            target = measure(following)
            delta = target-current
            if delta > 0 and rho not in (0, 1):
                estimate = delta*max(rho.numerator.bit_length(), rho.denominator.bit_length())
                if estimate > max_probability_bits:
                    raise PhysicalBudgetExceeded('probability_bit_budget')
            probability = acceptance(rho, delta)
            stats['probability_bits_peak'] = max(stats['probability_bits_peak'],
                probability.numerator.bit_length(), probability.denominator.bit_length())
            if probability == 1 or (probability and draw(probability.denominator) < probability.numerator):
                word, current = following, target
                stats['accepted_flips'] += 1
                minimum = min(minimum, current)
                changed = True
    except PhysicalBudgetExceeded as exc:
        reason = str(exc)
    if current == 0 and not satisfies(clauses, word):
        raise AssertionError('zero-energy witness failed the independent clause checker')
    return dict(status='SAT' if current == 0 else 'UNKNOWN', witness=word if current == 0 else None,
                reason='checked_zero_energy' if current == 0 else reason,
                final_word=word, final_energy=current, minimum_energy_seen=minimum, **stats)


def restart_sample(n, clauses, *, seed=0, max_attempts=8, ticks_per_attempt=1000,
                   max_random_bits=1_000_000):
    """Uniform restarts of zero-temperature local search; no general time guarantee.

    Initialization and per-run seed bits are counted, as are all sampler draws
    and neighbor inspections. The reset cost includes n spin writes per attempt.
    A strict local minimum triggers a reset; flat regions still use the tick cap.
    As with sample(), finite seeded traces are reproducibility controls, not
    implementations of an infinite ideal random-bit source.
    """
    clauses = _input(n, clauses)
    for value, name in ((max_attempts, 'attempt budget'), (ticks_per_attempt, 'tick budget'),
                        (max_random_bits, 'random-bit budget')):
        _natural(value, name)
    rng = random.Random(seed)
    attempts = []
    totals = dict(ticks=0, literal_inspections=0, random_bits=0,
                  initialization_random_bits=0, initialization_bit_writes=0)
    status, witness, reason = 'UNKNOWN', None, 'attempt_budget'
    for _ in range(max_attempts):
        if totals['random_bits']+n+64 > max_random_bits:
            reason = 'random_bit_budget'
            break
        initial, run_seed = rng.getrandbits(n), rng.getrandbits(64)
        totals['random_bits'] += n+64
        totals['initialization_random_bits'] += n+64
        totals['initialization_bit_writes'] += n
        answer = sample(n, clauses, rho=F(0), initial=initial, seed=run_seed,
                        max_ticks=ticks_per_attempt, stop_at_local_minimum=True,
                        max_random_bits=max_random_bits-totals['random_bits'])
        for key in ('ticks', 'literal_inspections', 'random_bits'):
            totals[key] += answer[key]
        attempts.append(dict(initial_word=initial, result=answer))
        if answer['status'] == 'SAT':
            status, witness, reason = 'SAT', answer['witness'], 'checked_zero_energy'
            break
        if answer['reason'] == 'random_bit_budget':
            reason = 'random_bit_budget'
            break
    return dict(status=status, witness=witness, reason=reason, attempts=attempts, **totals)


def chain(n, clauses, rho, *, max_states=64):
    """Exponential reference kernel, with explicit state-count budget."""
    clauses, rho = _input(n, clauses), _rho(rho)
    _natural(max_states, 'state budget')
    if n >= max_states.bit_length():
        raise PhysicalBudgetExceeded('state_enumeration_budget')
    energies = [energy(clauses, word) for word in range(1 << n)]
    rows = []
    for word, value in enumerate(energies):
        row = {word: F(1)}
        for j in range(n):
            target = word ^ (1 << j)
            probability = acceptance(rho, energies[target]-value)/(2*n)
            if probability:
                row[target] = probability
                row[word] -= probability
        rows.append(row)
    return energies, rows


def mean_hitting(rows, targets, start):
    """Exact finite-state reference; None denotes positive probability of never hitting."""
    targets = set(targets)
    size = len(rows)
    if not 0 <= start < size or any(not 0 <= j < size for j in targets):
        raise ValueError('state outside the kernel')
    if start in targets:
        return F(0)
    reachable, pending = set(), [start]
    while pending:
        word = pending.pop()
        if word not in reachable:
            reachable.add(word)
            if word not in targets:
                pending.extend(j for j, p in rows[word].items() if p and j not in reachable)
    can_hit = reachable & targets
    while True:
        following = can_hit | {i for i in reachable if any(p and j in can_hit for j, p in rows[i].items())}
        if following == can_hit:
            break
        can_hit = following
    if reachable - can_hit:
        return None
    transient = sorted(reachable-targets)
    indices = {word: j for j, word in enumerate(transient)}
    a = [[F(i == j)-rows[word].get(other, F(0)) for j, other in enumerate(transient)]+[F(1)]
         for i, word in enumerate(transient)]
    for column in range(len(a)):
        pivot = next(j for j in range(column, len(a)) if a[j][column])
        a[column], a[pivot] = a[pivot], a[column]
        scale = a[column][column]
        a[column] = [value/scale for value in a[column]]
        for j in range(len(a)):
            if j != column and a[j][column]:
                multiple = a[j][column]
                a[j] = [x-multiple*y for x, y in zip(a[j], a[column])]
    return a[indices[start]][-1]


def trap_cnf(n):
    _natural(n, 'variables')
    if n < 2:
        raise ValueError('at least two variables required')
    clauses = [(i,) for i in range(1, n+1)]
    for i in range(1, n+1):
        for j in range(i+1, n+1):
            clauses.extend([(-i, j), (i, -j)]*2)
    return tuple(clauses)


def trap_energy(n, k):
    return n-k+2*k*(n-k)


def trap_rates(n, rho):
    _natural(n, 'variables'); rho = _rho(rho)
    if n < 2:
        raise ValueError('at least two variables required')
    up, down = [], []
    for k in range(n+1):
        value = trap_energy(n, k)
        up.append(F(n-k, 2*n)*acceptance(rho, trap_energy(n, k+1)-value) if k < n else F(0))
        down.append(F(k, 2*n)*acceptance(rho, trap_energy(n, k-1)-value) if k else F(0))
    return up, down


def trap_summary(n, rho):
    up, down = trap_rates(n, rho)
    rho = _rho(rho)
    if rho == 0:
        return dict(mean_ticks=None, first_exit_mean_ticks=None, stationary_ground_probability=F(1),
                    stationary_scope='zero-temperature Gibbs limit; chain is reducible and need not approach it')
    differences = []
    for k in range(n):
        differences.append((1+(down[k]*differences[-1] if k else 0))/up[k])
    partition = sum(F(comb(n, k))*rho**trap_energy(n, k) for k in range(n+1))
    return dict(mean_ticks=sum(differences), first_exit_mean_ticks=1/up[0],
                stationary_ground_probability=1/partition,
                stationary_scope='exact invariant probability, not a bound on convergence time')


def deadline_bound(n, ticks, rho=None):
    """All-size proof above; finite checks alone do not establish this theorem."""
    _natural(n, 'variables'); _natural(ticks, 'ticks')
    if n < 2 or n % 2:
        raise ValueError('the stated bound requires even n>=2')
    cold = F(2)**(2-n//2)
    warm = F(127, 128)**n
    if rho is None:
        coefficient, regime = max(cold, warm), 'uniform over fixed temperatures'
    else:
        rho = _rho(rho)
        if rho == 0:
            return dict(probability_upper_bound=F(0), regime='absorbing initial trap')
        coefficient, regime = (cold, 'cold reversible bound') if rho**n <= F(1, 8) else (warm, 'warm domination bound')
    return dict(probability_upper_bound=min(F(1), (ticks+1)*coefficient), regime=regime)


def zero_temperature_restart_control(n):
    """Exact uniform-start analysis for this family, not a general SAT algorithm."""
    _natural(n, 'variables')
    if n < 2 or n % 2:
        raise ValueError('even n>=2 required')
    harmonic = [F(0)]
    for k in range(1, n+1):
        harmonic.append(harmonic[-1]+F(1, k))
    success, total = F(0), F(0)
    for k in range(n+1):
        mass = F(comb(n, k), 1 << n)
        success += mass*(F(1) if k > n//2 else F(1, 2) if k == n//2 else F(0))
        duration = 2+2*n*harmonic[k-1] if k == n//2 else 2*n*harmonic[min(k, n-k)]
        total += mass*duration
    return dict(success_probability_per_attempt=success, mean_ticks_to_either_endpoint=total,
                mean_ticks_until_success_with_endpoint_restarts=total/success,
                scope='Uniform initialization and detection of either endpoint; preparation/detection are extra polynomial work.')
