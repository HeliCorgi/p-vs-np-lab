#!/usr/bin/env python3
"""Audit a SAT proposal based on the distribution of violated-clause counts.

This is a bounded counterexample audit, not a new SAT solver or a new theorem
of complexity theory. All assignment and clause-subset enumeration is charged.

Proposed mechanism: if F has m clauses, its violation count E(x) has only m+1
possible values. Recovering the mass at zero from a short, efficiently computed
moment sequence would decide SAT. For the binomial moments

    B_t = sum_x choose(E(x), t),

the exact zero mass is sum_{t=0}^m (-1)^t B_t. Also B_t is the sum, over all
t-element subsets of the input clause POSITIONS, of the number of assignments
falsifying them simultaneously. Each such term is either zero or 2^(n-|scope|).
The implemented evaluator costs sum_{t<=r} choose(m,t) subset visits through r.
The small output vector alone does not give a polynomial running-time bound.

All-size adversarial argument (standard parity linear algebra): take any
connected simple cubic graph with q vertices and n=3q/2 edges. Put an edge bit
on each edge and a parity equation at each vertex. Encode each equation by its
four proper 3-clauses. At a violated equation exactly ONE clause is false, so
E(x) is exactly the number of violated vertex equations. The incidence map has
image the even-parity subspace and kernel dimension n-q+1. To see surjectivity,
solve any even demand on a spanning tree by peeling leaves; the last equation
then follows from the parity condition. Every image word has 2^(n-q+1) fibers.

Even total charge gives SAT; odd total charge gives UNSAT. Their histograms are
H_b(j)=2^(n-q+1)*choose(q,j) if j has parity b, and zero otherwise. For t<q,
choose(q,j)*choose(j,t)=choose(q,t)*choose(q-t,j-t), so summing either parity gives

    B_t = choose(q,t) * 2^(n-t),  0 <= t < q.

Thus the first q-1 nonconstant aggregate moments, including all power moments
of those orders, coincide. At order q they differ. Prisms give all even q>=6;
K4 supplies q=4. This rules out deciding from such a truncated aggregate alone,
even for this easy XOR fragment. It does NOT rule out a polynomial algorithm
that computes linearly many moments or uses additional formula information.

Recovering all moments of an arbitrary CNF in polynomial time would compute
exact #SAT by the displayed identity, a stronger sufficient task than SAT.
No fast general moment construction is supplied. The ordinary parity and
inclusion-exclusion facts used here are not claimed as new research.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from math import comb, factorial
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from pnp_lab.sat_scaling import (check_row_contradiction, gaussian,
                                recognize_xor, satisfies, validate, xor_clauses)


class AuditBudgetExceeded(RuntimeError):
    """A reference enumeration exceeds its explicit budget; no SAT answer."""


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _input(n, clauses):
    clauses = tuple(tuple(c) for c in clauses)
    validate(n, clauses)
    if any(len(c) > 3 for c in clauses):
        raise ValueError("this audit accepts clauses of width at most three")
    return clauses


def _masks(clauses):
    return tuple((sum(1 << (abs(lit) - 1) for lit in c),
                  sum(1 << (abs(lit) - 1) for lit in c if lit < 0)) for c in clauses)


def violation_histogram(n, clauses, *, assignment_limit=1 << 18):
    """Exact reference histogram, by exhaustive assignment enumeration."""
    clauses = _input(n, clauses)
    _natural(assignment_limit, "assignment_limit")
    if n >= assignment_limit.bit_length():
        raise AuditBudgetExceeded("assignment enumeration budget")
    masks = _masks(clauses)
    histogram = [0] * (len(clauses) + 1)
    for word in range(1 << n):
        histogram[sum((word & scope) == bad for scope, bad in masks)] += 1
    return histogram


def binomial_moments(histogram, order):
    _natural(order, "order")
    histogram = tuple(histogram)
    if not histogram or any(type(h) is not int or h < 0 for h in histogram):
        raise ValueError("nonempty histogram of nonnegative integer counts required")
    return [sum(h * comb(j, t) for j, h in enumerate(histogram) if j >= t)
            for t in range(order + 1)]


def power_moments(histogram, order):
    _natural(order, "order")
    histogram = tuple(histogram)
    if not histogram or any(type(h) is not int or h < 0 for h in histogram):
        raise ValueError("nonempty histogram of nonnegative integer counts required")
    return [sum(h * j ** t for j, h in enumerate(histogram)) for t in range(order + 1)]


def subset_binomial_moments(n, clauses, order, *, subset_limit=100_000):
    """Compute moments from clause intersections, without enumerating assignments.

    Duplicate clauses are separate positions, as in the definition of E.
    Incompatible falsification patterns contribute zero. The subset count is
    the full enumeration count, including subsets rejected for inconsistency.
    """
    clauses = _input(n, clauses)
    _natural(order, "order")
    _natural(subset_limit, "subset_limit")
    if order > len(clauses):
        raise ValueError("order exceeds the input clause count")
    visits = sum(comb(len(clauses), t) for t in range(order + 1))
    if visits > subset_limit:
        raise AuditBudgetExceeded("clause-subset enumeration budget")
    masks = _masks(clauses)
    moments = []
    consistent = []
    for t in range(order + 1):
        value = hits = 0
        for indices in combinations(range(len(clauses)), t):
            scope = bad = 0
            for index in indices:
                next_scope, next_bad = masks[index]
                if (scope & next_scope) & (bad ^ next_bad):
                    break
                scope |= next_scope
                bad |= next_bad
            else:
                value += 1 << (n - scope.bit_count())
                hits += 1
        moments.append(value)
        consistent.append(hits)
    return dict(moments=moments, subsets_examined=visits,
                consistent_subsets_by_order=consistent)


def zero_mass(moments, *, maximum_violations):
    """Invert exact moments, with a supplied VALID upper bound on E.

    This checks sequence length, not whether the caller's moments or bound are
    truthful. It is not an independent UNSAT certificate verifier.
    """
    _natural(maximum_violations, "maximum_violations")
    moments = tuple(moments)
    if len(moments) != maximum_violations + 1:
        raise ValueError("a complete moment sequence for the supplied bound is required")
    if any(type(v) is not int or v < 0 for v in moments):
        raise ValueError("moments must be nonnegative integer counts")
    return sum((-1) ** t * value for t, value in enumerate(moments))


def bonferroni_bounds(moments):
    """Bounds from an exact prefix: odd partial sums are lower bounds."""
    moments = tuple(moments)
    if not moments or any(type(v) is not int or v < 0 for v in moments):
        raise ValueError("nonempty exact moment prefix required")
    lower, upper, partial = 0, moments[0], 0
    for t, value in enumerate(moments):
        partial += (-1) ** t * value
        if t % 2:
            lower = max(lower, partial)
        else:
            upper = min(upper, partial)
    if lower > upper:
        raise ValueError("inconsistent moment prefix")
    return lower, upper


def prism_edges(r):
    _natural(r, "prism cycle size")
    if r < 3:
        raise ValueError("a simple prism requires cycle size at least three")
    return tuple(sorted({tuple(sorted(e)) for i in range(r) for e in
                         ((i, (i + 1) % r), (r + i, r + (i + 1) % r), (i, r + i))}))


def cubic_cnf(q, edges, charges):
    """Proper 3-CNF for a connected simple cubic parity graph."""
    _natural(q, "vertices")
    edges = tuple(tuple(e) for e in edges)
    charges = tuple(charges)
    if q < 4 or len(charges) != q or any(type(b) is not int or b not in (0, 1) for b in charges):
        raise ValueError("one Boolean charge per vertex is required")
    if any(len(e) != 2 or any(type(v) is not int or not 0 <= v < q for v in e)
           or e[0] >= e[1] for e in edges) or len(set(edges)) != len(edges):
        raise ValueError("edges must be distinct ordered pairs u<v")
    incidence = [[] for _ in range(q)]
    adjacency = [set() for _ in range(q)]
    for variable, (u, v) in enumerate(edges, 1):
        incidence[u].append(variable)
        incidence[v].append(variable)
        adjacency[u].add(v)
        adjacency[v].add(u)
    if any(len(row) != 3 for row in incidence):
        raise ValueError("every vertex must have degree three")
    seen, pending = set(), [0]
    while pending:
        v = pending.pop()
        if v not in seen:
            seen.add(v)
            pending.extend(adjacency[v] - seen)
    if len(seen) != q:
        raise ValueError("graph must be connected")
    return tuple(c for row, charge in zip(incidence, charges) for c in xor_clauses(row, charge))


def audit():
    cases = [("K4", 4, tuple(combinations(range(4), 2)))]
    cases += [(f"prism_{r}", 2 * r, prism_edges(r)) for r in range(3, 7)]
    rows = []
    for name, q, edges in cases:
        n = len(edges)
        fibers = 1 << (n - q + 1)
        records = []
        for parity in (0, 1):
            charges = (parity,) + (0,) * (q - 1)
            cnf = cubic_cnf(q, edges, charges)
            histogram = violation_histogram(n, cnf)
            expected = [fibers * comb(q, j) if j <= q and j % 2 == parity else 0
                        for j in range(len(cnf) + 1)]
            if histogram != expected:
                raise AssertionError("raw-CNF histogram disagrees with the incidence-map prediction")
            moments = binomial_moments(histogram, len(cnf))
            expected_prefix = [comb(q, t) * (1 << (n - t)) for t in range(q)]
            if moments[:q] != expected_prefix or zero_mass(moments, maximum_violations=len(cnf)) != histogram[0]:
                raise AssertionError("moment identity or exact zero-mass recovery failed")
            evaluated_order = len(cnf) if q == 4 else 3
            direct = subset_binomial_moments(n, cnf, evaluated_order)
            if direct['moments'] != moments[:evaluated_order + 1]:
                raise AssertionError("independent clause-subset moments disagree")
            equations = recognize_xor(n, cnf)
            if equations is None:
                raise AssertionError("the original CNF parity structure was not recovered")
            control = gaussian(n, equations)
            if control['status'] != ('SAT' if parity == 0 else 'UNSAT'):
                raise AssertionError("Gaussian control has the wrong status")
            if parity == 0:
                if not satisfies(cnf, control['witness']):
                    raise AssertionError("SAT model does not satisfy the original clauses")
            elif not check_row_contradiction(equations, control['contradiction']):
                raise AssertionError("UNSAT row-sum certificate did not replay")
            occurrences = Counter(abs(lit) for clause in cnf for lit in clause)
            if len(set(cnf)) != len(cnf) or set(occurrences.values()) != {8}:
                raise AssertionError("clause distinctness or occurrence bound failed")
            records.append(dict(
                total_charge_parity=parity, clauses_sha256=sha256(json.dumps(cnf).encode()).hexdigest(),
                violation_histogram=histogram, binomial_moments=moments,
                power_moments=power_moments(histogram, q), model_count=histogram[0],
                low_order_zero_mass_bounds=bonferroni_bounds(moments[:q]),
                subset_order_actually_evaluated=evaluated_order, subset_evaluation=direct,
                gaussian_control=control, gaussian_certificate_checked=True))
        even, odd = records
        if (even['power_moments'][:q] != odd['power_moments'][:q]
                or even['power_moments'][q] - odd['power_moments'][q] != fibers * factorial(q)
                or even['binomial_moments'][q] - odd['binomial_moments'][q] != fibers):
            raise AssertionError("claimed first distinguishing moment is wrong")
        rows.append(dict(graph=name, vertices=q, variables=n, clauses=4*q,
                         edges=edges, maximum_variable_occurrence=8,
                         matching_nonconstant_moment_orders=q-1, first_distinguishing_order=q,
                         subset_visits_through_distinguishing_order=sum(comb(4*q, t) for t in range(q+1)),
                         cases=records))
    return dict(
        all_checks_passed=True, proposed_mechanism='SAT from cheaply computed violation-count moments',
        cases=rows, formula_count=2*len(rows),
        assignments_enumerated=sum(2*(1 << row['variables']) for row in rows),
        subset_visits_executed=sum(case['subset_evaluation']['subsets_examined'] for row in rows for case in row['cases']),
        largest_matching_nonconstant_order=max(row['matching_nonconstant_moment_orders'] for row in rows),
        decision='Reject a universal truncated-aggregate shortcut; no fast full-moment construction obtained.',
        complete_moment_algorithm_polynomial_time_proved=False,
        all_algorithm_lower_bound_proved=False, p_vs_np_resolved=False, p_vs_np_probability=None,
        scope='Exact finite counterchecks of the all-size standard parity argument in this script. '
              'No new theorem of complexity theory, new Lean proof, or evidence distinguishing P from NP. '
              'The counterexample formulas themselves are solved by recovered Gaussian elimination.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), indent=2, sort_keys=True) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'violation_moments.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
