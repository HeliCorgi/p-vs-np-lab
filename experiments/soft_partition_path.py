#!/usr/bin/env python3
"""A different SAT candidate: adaptive evaluation of a soft counting polynomial.

This is a costed reference audit, NOT a polynomial-time SAT algorithm.
We use standard positive-polynomial/annealing ideas, not a novelty claim.
Related background: Patel and Regts, SIAM J. Comput. 46 (2017),
Deterministic Polynomial-Time Approximation Algorithms for Partition Functions
and Graph Polynomials, doi:10.1137/16M1101003. Their efficient coefficient
algorithms have structural hypotheses; we do not assert they cover general CNF.

For an n-variable, m-clause CNF, E(x) is its number of false clauses and
H(q)=sum_x q^E(x). At q*=2^(-n-2), SAT implies H(q*)>=1; UNSAT implies
H(q*)<=2^n q*=1/4. Thus an estimate with certified interval entirely on one
side of 1/2 decides SAT, with a polynomial-bit rational evaluation point.

There IS a uniform polynomial-length path to q*, even when complex zeros
approach zero exponentially closely. For q>0 and |z-q|<=q/(4m),
  |H(z)-H(q)|/H(q) <= (1+1/(4m))^m-1 < sum_{j>=1} 4^-j = 1/3.
The inequality follows termwise from nonnegative coefficients and degree<=m.
Hence that disk is zero-free. Steps q' = max(q*,q*(1-1/(8m))) stay inside
half its radius. At most D=8m(n+2) steps suffice, since (1-1/(8m))^D
<=exp(-(n+2))<2^(-n-2). Each path rational has O(D log(m+1)+n) bits.

The missing computation is visible in the exact local transfer:
  H(q(1-h))/H(q) = sum_{j=0}^m (-h)^j B_j(q),
  B_j(q) = sum_x binom(E(x),j) q^E(x) / H(q).
Here B_0=1, 0<=B_j<=binom(m,j), and 0<=h<=1/(8m). For each exponent E,
the binomial expansion is alternating with decreasing terms. Consecutive
truncations of orders K,K+1 therefore bracket the ratio; their gap is at
most 8^(-K-1). The ratio itself lies in [7/8,1] by Bernoulli's inequality.

Choose K>=1 with 8^(K+1)>=32D. If each B_j(q), 1<=j<=K+1, is supplied
within eps=1/(1024D(K+2)), widen each truncation by (K+1)eps. The ratio
interval width is <=1/(32D)+1/(512D)<1/(16D), or <=1/(14D) relative to
the true ratio. Multiply these intervals, rounding outwards to a dyadic
grid of mesh<=1/(256D). Ratios are at most 1, so total rounding error is
<=1/256, not amplified by subsequent steps. The final enclosure satisfies
  lower >= (1-1/(14D))^D H(q*) - 1/256,
  upper <= (1+1/(14D))^D H(q*) + 1/256.
For SAT, lower>=13/14-1/256>1/2; for UNSAT,
upper<=exp(1/14)/4+1/256<1/2. Stored value numerators have O(n+log D) bits;
moment magnitudes need O(K log(m+1)) bits, with polynomial requested precision.
Consequently a uniform polynomial-time provider of THESE weighted moments
to the stated precision would give P=NP. It has NOT been constructed.

The reference provider below enumerates all 2^n assignments to obtain H's
coefficients, then evaluates local moments with rational arithmetic. This
explicit exponential preparation is charged, capped, and never treated as
free. The experiment checks the transfer and intervals; it cannot validate
the missing provider. A reused parity example checks why a low-order jet at
q=1 cannot in general be transported exactly to later centers without new
formula information. It does not rule out a provider using that information.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import comb
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src"))
from experiments.violation_moments import (AuditBudgetExceeded, binomial_moments,
    cubic_cnf, prism_edges, violation_histogram)


def parameters(n, m):
    if any(type(v) is not int or v < 0 for v in (n, m)):
        raise ValueError("nonnegative integer dimensions required")
    bound = max(1, 8*m*(n+2))
    order = 1
    while 8**(order+1) < 32*bound:
        order += 1
    return dict(target=Q(1, 2**(n+2)), step_bound=bound, order=order,
                moment_error=Q(1, 1024*bound*(order+2)),
                grid_bits=(256*bound-1).bit_length())


def path(n, m, *, step_limit=100_000):
    p = parameters(n, m)
    if type(step_limit) is not int or step_limit < 0:
        raise ValueError("nonnegative integer step limit required")
    if not m:
        return
    q, count = Q(1), 0
    while q > p['target']:
        if count >= step_limit:
            raise AuditBudgetExceeded("path-step budget; no SAT decision")
        next_q = max(p['target'], q*Q(8*m-1, 8*m))
        yield q, next_q
        q, count = next_q, count+1
        assert count <= p['step_bound']


def value_and_moments(histogram, q, order):
    """Reference only: coefficients were obtained by charged enumeration."""
    if not histogram or any(type(v) is not int or v < 0 for v in histogram):
        raise ValueError("nonnegative integer histogram required")
    if not any(histogram) or not Q(0) < q <= 1:
        raise ValueError("positive polynomial and positive center required")
    if type(order) is not int or order < 0:
        raise ValueError("nonnegative integer order required")
    weighted = [count*q**j for j, count in enumerate(histogram)]
    total = sum(weighted, Q(0))
    moments = [sum((v*comb(e, j) for e, v in enumerate(weighted) if e>=j), Q(0))/total
               for j in range(order+1)]
    return total, moments


def ratio_interval(m, moments, h, error=Q(0)):
    """Sound if each supplied moment is within 'error' of its true value."""
    if type(m) is not int or m < 1 or not 0 <= h <= Q(1, 8*m):
        raise ValueError("invalid degree/step")
    if len(moments) < 3 or moments[0] != 1 or error < 0:
        raise ValueError("orders 0..K+1, K>=1, and nonnegative error required")
    terms = [(-h)**j*v for j, v in enumerate(moments)]
    a, b = sum(terms[:-1]), sum(terms)
    uncertainty = (len(moments)-1)*error
    lower, upper = max(Q(7, 8), min(a,b)-uncertainty), min(Q(1), max(a,b)+uncertainty)
    if lower > upper:
        raise ValueError("inconsistent moment estimates")
    return lower, upper


def dyadic(value, bits, upper=False):
    scaled = value * 2**bits
    numerator = -((-scaled.numerator)//scaled.denominator) if upper else scaled.numerator//scaled.denominator
    return Q(numerator, 2**bits)


def evaluate_histogram(n, histogram, *, step_limit=100_000, noisy=False):
    """Audit an already-known histogram; NOT an efficient CNF input interface."""
    if (not histogram or any(type(v) is not int or v < 0 for v in histogram)
            or sum(histogram) != 2**n):
        raise ValueError("histogram must count exactly 2^n assignments")
    m = len(histogram)-1
    p = parameters(n, m)
    lower = upper = Q(2**n)
    calls = visits = steps = max_bits = 0
    for q, next_q in path(n, m, step_limit=step_limit):
        value, moments = value_and_moments(histogram, q, p['order']+1)
        calls += 1
        visits += len(histogram)*(p['order']+2)
        if noisy:
            moments = [moments[0]] + [v+(-1)**(j+steps)*p['moment_error']
                                     for j,v in enumerate(moments[1:], 1)]
        lo, hi = ratio_interval(m, moments, 1-next_q/q, p['moment_error'])
        next_value, _ = value_and_moments(histogram, next_q, 0)
        assert lo <= next_value/value <= hi
        lower = dyadic(lower*lo, p['grid_bits'])
        upper = dyadic(upper*hi, p['grid_bits'], upper=True)
        assert lower <= next_value <= upper
        max_bits = max(max_bits, q.denominator.bit_length(), next_q.denominator.bit_length())
        steps += 1
    target_value, _ = value_and_moments(histogram, p['target'], 0)
    assert lower <= target_value <= upper
    status = 'SAT' if lower>Q(1,2) else 'UNSAT' if upper<Q(1,2) else 'UNKNOWN'
    assert status == ('SAT' if histogram[0] else 'UNSAT')
    assert target_value>=1 if histogram[0] else target_value<=Q(1,4)
    return dict(status=status, steps=steps, step_bound=p['step_bound'], order=p['order'],
                weighted_moment_calls=calls, reference_moment_cell_visits=visits,
                reference_validation_evaluations=steps+1,
                interval=[str(lower), str(upper)],
                maximum_path_denominator_bits=max_bits,
                bounded_moment_perturbations=noisy)


def evaluate_cnf(n, clauses, *, assignment_limit=1<<16, step_limit=100_000, noisy=False):
    clauses = tuple(tuple(c) for c in clauses)
    histogram = violation_histogram(n, clauses, assignment_limit=assignment_limit)
    row = evaluate_histogram(n, histogram, step_limit=step_limit, noisy=noisy)
    row.update(n=n, m=len(clauses), satisfying_assignments=histogram[0],
               reference_assignments_enumerated=2**n,
               reference_clause_checks=2**n*len(clauses))
    return row


def matched_jet_control():
    """Reuse the known parity control; no new obstruction theorem claimed."""
    edges = prism_edges(4)
    formulas = [cubic_cnf(8, edges, (b,0,0,0,0,0,0,0)) for b in (0,1)]
    histograms = [violation_histogram(12, f) for f in formulas]
    initial = [binomial_moments(h, 7) for h in histograms]
    assert initial[0] == initial[1]
    later = [value_and_moments(h, Q(1,2), 1)[1][1] for h in histograms]
    p = parameters(12,32)
    assert p['order']+1 <= 7
    assert abs(later[0]-later[1]) > 2*p['moment_error']
    return dict(n=12, clauses=32, matching_initial_orders=list(range(8)),
                required_initial_order=p['order']+1,
                initial_unnormalized_moments=initial[0],
                satisfying_assignments=[h[0] for h in histograms],
                first_weighted_moment_at_half=[str(v) for v in later],
                required_additive_error=str(p['moment_error']),
                later_moment_gap_exceeds_twice_tolerance=True,
                reference_assignments_enumerated=8192,
                scope='Finite check of the previously proved parity family. '
                      'A low-order initial jet alone does not supply fresh weighted moments; '
                      'algorithms using other formula information are not excluded.')


def audit():
    rows = []
    proper = list(product((1,-1),(2,-2),(3,-3)))
    for mask in range(256):
        clauses = [c for i,c in enumerate(proper) if mask>>i&1]
        rows.append(dict(case=f'proper3-{mask}', **evaluate_cnf(3,clauses)))
    mixed = [(1,), (-1,), (2,), (-2,), (1,2), (-1,-2)]
    for mask in range(64):
        clauses = [c for i,c in enumerate(mixed) if mask>>i&1]
        rows.append(dict(case=f'mixed2-{mask}', **evaluate_cnf(2,clauses,noisy=True)))
    for n,clauses in [(0,[]),(0,[()]),(2,[(),(1,),(-2,)]),(3,[(1,),(1,),(-1,)])]:
        rows.append(dict(case=f'edge-{len(rows)}', **evaluate_cnf(n,clauses,noisy=True)))
    control = matched_jet_control()
    return dict(all_checks_passed=True, cases=rows, matched_jet_control=control,
                case_count=len(rows),
                status_counts={s:sum(r['status']==s for r in rows) for s in ('SAT','UNSAT','UNKNOWN')},
                reference_assignments_enumerated=sum(r['reference_assignments_enumerated'] for r in rows)
                    +control['reference_assignments_enumerated'],
                weighted_moment_calls=sum(r['weighted_moment_calls'] for r in rows),
                maximum_steps=max(r['steps'] for r in rows),
                maximum_order=max(r['order'] for r in rows),
                polynomial_path_constructed=True,
                polynomial_weighted_moment_provider_constructed=False,
                general_polynomial_sat_algorithm=False, p_vs_np_resolved=False,
                decision='The geometric path is polynomial; fresh weighted moments remain unimplemented '
                         'in polynomial time. Do not adopt this as a complete-proof route or optimize '
                         'the enumerating reference provider.',
                scope='Exact rational verification of a conditional evaluation construction. '
                      'All reference assignment enumeration is charged; no new Lean proof or novelty claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    report = json.dumps(audit(), indent=2, sort_keys=True)+'\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir/'soft_partition_path.json').write_text(report, encoding='utf-8')
    else:
        print(report, end='')


if __name__ == '__main__':
    main()
