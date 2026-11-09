#!/usr/bin/env python3
"""Audit a possible improvement to OpenAI's ETH auxiliary construction.

Source: openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae,
preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/
build/main_full_version.tex, subsection preview-auxiliary, Step 2.
This is an independent implementation of the stated finite construction,
not an upstream theorem replay, new SAT solver, or novelty claim.

There are Q commuting swaps on ([r] x [r])^Q, dimension D=r^(2Q).
Let W=sum_s (I-Pi_s)/2, V=prod_s Pi_s and M=V*f(W). A tensor basis
vector with j antisymmetric factors has eigenvalues j for W and (-1)^j
for V. With a=r(r-1)/2 and b=r(r+1)/2, its multiplicity is

    w_j = choose(Q,j) a^j b^(Q-j).

Consequently rank(I-M)=sum_{j: f(j) != (-1)^j} w_j. Computing these Q+1
weights avoids constructing D coordinates. It does not construct the actual
measurement rows, replacement forms, or SAT count after occurrence substitution.

Improvement tested: permit ANY rational polynomial of degree at most d, rather
than only interpolate d+1 consecutive spectral levels. Exact optimization is
finite: an optimum matches at least d+1 levels, because fewer matches can be
extended by interpolation, strictly increasing their positive total weight.
Every optimum is therefore determined by some d+1 matched nodes. Enumerating
all choose(Q+1,d+1) choices covers it. This search is explicitly budgeted.

Two universal lower bounds apply within this scalar-polynomial construction.
If f is nonconstant, f^2-1 has degree at most 2d, hence at most 2d roots.
The total matched weight is at most the sum of the 2d largest weights.
Constants +/-1 match just one parity (other constants match no level).
Also every d+2 consecutive levels contain an error: the (d+1)-st finite
difference of (-1)^j is nonzero whereas that of f is zero. A path DP finds
the minimum weight of a set hitting every such window. Both are lower bounds,
not a characterization of realizable error sets. Exhaustive interpolation
supplies exact optima only for the explicitly listed finite cases.

A separate all-size check rejects merely retuning the paper's *explicit*
coordinate/Taylor enumerations into polynomial time. For n>=6, r>=2, R>=1,
Q>=1, that implementation pays at least D>=2^(2Q) coordinate visits and
S=sum_{j<=min(floor(3nR/Q),n)} 2^j choose(n,j) Taylor calls. If q>=n,
S=3^n. Otherwise S>=2^q and 2Q(q+1)>6n. In either case

    log2(max(D,S)) > sqrt(6n)-1.

For r=1 the local assignment scan is 2^n instead. This is a lower bound on
these enumerations, not on the upstream algorithm under every implementation,
its sharper appendix constructions, or general SAT algorithms. Avoiding
explicit coordinates or Taylor calls changes the premises. Spectral rank
compression here removes neither the actual measurement construction nor
the formula-dependent counting obligation.

The paper's Step 4 has additional sufficient balancing conditions
12D^2 <= M <= 3n and 2Qr^2 <= n. Keeping them forces 4r^(4Q) <= n,
so for r>=2, Q <= (log2(n)-2)/4. Even R=1 then leaves Taylor order
Omega(n/log n). Also at least one variable group has size >=n/r>=sqrt(2nQ),
so enumerating its assignments costs at least 2^sqrt(2n). This conclusion
still applies if the auxiliary rank is computed implicitly, as here. A new
incidence-balancing theorem or a different way to evaluate the sums is needed
to escape these particular premises. These sufficient conditions are not
asserted to be necessary for every possible design or for the sharper appendix.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb, isqrt
from pathlib import Path

PIN = '4eaee87548250b2682affda7d05d947c05554bae'
PAPER = 'preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex'


class RepairBudgetExceeded(RuntimeError):
    pass


def natural(n, name):
    if type(n) is not int or n < 0:
        raise ValueError(f'{name} must be a nonnegative integer')


def weights(r, q):
    natural(r, 'groups'); natural(q, 'swap positions')
    if r < 2:
        raise ValueError('at least two groups required by this audit')
    a, b = r*(r-1)//2, r*(r+1)//2
    return [comb(q, j)*a**j*b**(q-j) for j in range(q+1)]


def interpolate(nodes):
    """Newton coefficients for f(j)=(-1)^j at distinct nonnegative nodes."""
    nodes = tuple(nodes)
    if not nodes or any(type(j) is not int or j < 0 for j in nodes) or len(set(nodes)) != len(nodes):
        raise ValueError('distinct nonnegative interpolation nodes required')
    coefficients = [Fraction((-1)**j) for j in nodes]
    for k in range(1, len(nodes)):
        for i in range(len(nodes)-1, k-1, -1):
            coefficients[i] = (coefficients[i]-coefficients[i-1])/(nodes[i]-nodes[i-k])
    return tuple(coefficients)


def evaluate(nodes, coefficients, x):
    if not coefficients or len(nodes) != len(coefficients):
        raise ValueError('one Newton coefficient per node required')
    value = coefficients[-1]
    for i in range(len(coefficients)-2, -1, -1):
        value = coefficients[i] + (x-nodes[i])*value
    return value


def matching_levels(q, nodes, coefficients):
    return tuple(j for j in range(q+1) if evaluate(nodes, coefficients, j) == (-1)**j)


def rank_defect(r, q, nodes, coefficients):
    matches = set(matching_levels(q, nodes, coefficients))
    return sum(w for j, w in enumerate(weights(r, q)) if j not in matches)


def lower_bounds(r, q, degree):
    natural(degree, 'degree')
    if degree > q:
        raise ValueError('degree exceeds the spectral range')
    w = weights(r, q)
    total = sum(w)
    parity = max(sum(w[::2]), sum(w[1::2]))
    root_bound = total-max(parity, sum(sorted(w, reverse=True)[:2*degree]))
    # State = consecutive levels since the last error, at most degree+1.
    costs = {0: 0}
    for weight in w:
        following = {0: min(costs.values())+weight}
        for run, cost in costs.items():
            if run < degree+1:
                following[run+1] = cost
        costs = following
    window_bound = min(costs.values())
    return dict(root_count=root_bound, consecutive_window=window_bound,
                combined=max(root_bound, window_bound))


def optimize(q, degree, *, groups=(2, 3, 4), candidate_limit=10_000):
    """Exhaust all interpolation choices, sharing candidates across group counts."""
    natural(q, 'swap positions'); natural(degree, 'degree'); natural(candidate_limit, 'candidate budget')
    if degree > q:
        raise ValueError('degree exceeds the spectral range')
    groups = tuple(groups)
    if not groups or len(set(groups)) != len(groups):
        raise ValueError('distinct group counts required')
    ws = {r: weights(r, q) for r in groups}
    count = comb(q+1, degree+1)
    if count > candidate_limit:
        raise RepairBudgetExceeded('exhaustive interpolation budget')
    best = {r: None for r in groups}
    # Include constants in the baseline; a larger degree is permission, not
    # an obligation to choose a nonconstant polynomial.
    baseline = {r: min(sum(w[::2]), sum(w[1::2])) for r, w in ws.items()}
    for nodes in combinations(range(q+1), degree+1):
        coefficients = interpolate(nodes)
        matches = matching_levels(q, nodes, coefficients)
        for r, w in ws.items():
            defect = sum(w)-sum(w[j] for j in matches)
            if best[r] is None or defect < best[r]['rank_defect']:
                best[r] = dict(rank_defect=defect, nodes=nodes,
                               newton_coefficients=[[c.numerator, c.denominator] for c in coefficients],
                               matched_levels=matches)
            if nodes[-1]-nodes[0] == degree:
                baseline[r] = min(baseline[r], defect)
    rows = []
    for r in groups:
        bounds = lower_bounds(r, q, degree)
        if not bounds['combined'] <= best[r]['rank_defect'] <= baseline[r]:
            raise AssertionError('rank bounds or baseline comparison failed')
        rows.append(dict(groups=r, positions=q, degree_budget=degree, dimension=r**(2*q),
                         weights=ws[r], optimum=best[r], lower_bounds=bounds,
                         consecutive_or_constant_rank_defect=baseline[r],
                         improves_consecutive_or_constant=best[r]['rank_defect'] < baseline[r],
                         candidate_count=count))
    return rows


def taylor_calls(n, q):
    natural(n, 'variables'); natural(q, 'Taylor order')
    if q >= n:
        return 3**n
    return sum((1 << j)*comb(n, j) for j in range(q+1))


def optimistic_retuning(n):
    """Exact minimization of a LOWER bound, ignoring measurements/local scans.

    R=1 and r=2 minimize the two costs under inspection. We minimize the
    floor-log of their maximum over every Q>=1. Q>n cannot improve the
    answer: its coordinate cost exceeds 2^(2n), while Q=1 costs at most 3^n.
    """
    natural(n, 'variables')
    if n < 6:
        raise ValueError('all-size bound is stated for n>=6')
    cached = {}
    best = None
    for points in range(1, n+1):
        order = min(3*n//points, n)
        if order not in cached:
            cached[order] = taylor_calls(n, order).bit_length()-1
        cost = max(2*points, cached[order])
        if best is None or cost < best['floor_log2_work_lower_bound']:
            best = dict(points=points, order=order, floor_log2_work_lower_bound=cost)
    threshold = isqrt(6*n)-1
    if best['floor_log2_work_lower_bound'] < threshold:
        raise AssertionError('enumeration contradicts the all-size lower bound')
    return dict(variables=n, all_size_guaranteed_log2_lower_bound=threshold,
                optimistic_optimum=best,
                scope='Optimistic lower bound for explicit coordinates and Taylor calls; not measured SAT time.')


def balance_requirements(n):
    """Necessary restrictions when retaining the overview's sufficient hypotheses."""
    natural(n, 'variables')
    if n < 64:
        raise ValueError('no r>=2, Q>=1 satisfies 4*r^(4Q)<=n below 64')
    max_points = ((n.bit_length()-1)-2)//4
    return dict(variables=n, largest_possible_Q=max_points,
                taylor_order_lower_bound=min(n, 3*n//max_points),
                largest_group_size_lower_bound=isqrt(2*n-1)+1,
                hypotheses='r>=2, Q>=1, R>=1, M<=3n, 12*r^(4Q)<=M, 2*Q*r^2<=n',
                scope='Bounds if retaining these sufficient balancing conditions and explicit assignment/Taylor scans; not necessary conditions for all designs.')


def audit():
    cases = []
    unique_candidates = spectral_evaluations = 0
    for q in (4, 8, 12):
        for d in range(6 if q >= 8 else 5):
            rows = optimize(q, d)
            cases.extend(rows)
            unique_candidates += rows[0]['candidate_count']
            spectral_evaluations += rows[0]['candidate_count']*(q+1)
    # Large implicit spectral calculations: none of the D coordinates is built.
    implicit = []
    for r, q, d in ((2, 256, 3), (2, 256, 15), (4, 256, 31), (16, 1024, 63)):
        w = weights(r, q)
        if sum(w) != r**(2*q):
            raise AssertionError('spectral dimension mismatch')
        implicit.append(dict(groups=r, positions=q, degree_budget=d, spectral_levels=q+1,
                             dimension_bit_length=(r**(2*q)).bit_length(),
                             minimum_defect_fraction_lower_bound=str(Fraction(lower_bounds(r, q, d)['combined'], sum(w)))))
    return dict(all_checks_passed=True, upstream_commit=PIN,
                upstream_source_url=f'https://github.com/openai/math/blob/{PIN}/{PAPER}',
                upstream_source_sha256='b2e6159d4fb7ea6aa4f89ac15605152b0333a5f7cafe93323492bc20a5c066aa',
                source_sections=['preview-auxiliary Steps 2 and 4', 'preview-interpolation', 'preview-parameters'],
                cases=cases, optimization_cases=len(cases),
                interpolation_candidates_evaluated=unique_candidates,
                spectral_level_evaluations=spectral_evaluations,
                strict_improvements_over_consecutive_or_constant=sum(row['improves_consecutive_or_constant'] for row in cases),
                implicit_spectral_cases=implicit,
                explicit_retuning=[optimistic_retuning(n) for n in (16, 64, 256, 1024, 4096)],
                balance_requirements=[balance_requirements(1 << bits) for bits in (10, 20, 40, 80)],
                finite_improvement_scope='The one improved auxiliary case retains over 37% defective directions; it is not a full small-tail SAT design or an end-to-end runtime improvement.',
                core_obligation='Construct and use actual occurrence-dependent measurements and recover the count with polynomial total bit cost; rank totals alone do not supply this.',
                upstream_kernel_replayed=False, general_polynomial_sat_algorithm_obtained=False,
                p_vs_np_resolved=False,
                scope='Exact finite optima within f(W), plus elementary all-size bounds on that ansatz and the stated explicit enumerations. No lower bound for all SAT algorithms or contradiction of the upstream subexponential theorem. Existing upstream snapshot remains unchanged.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), indent=2, sort_keys=True) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir/'eth_polynomial_repair.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
