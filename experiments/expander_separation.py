"""Exact finite support counts and rational checks of the asymptotic budgets."""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path


def boundary(supports, selected):
    counts = {}
    for i in selected:
        for v in supports[i]:
            counts[v] = counts.get(v, 0) + 1
    return frozenset(v for v, count in counts.items() if count == 1)


def connected(supports, selected):
    selected = set(selected)
    if not selected:
        return False
    reached = {min(selected)}
    while True:
        added = {j for j in selected - reached
                 if any(set(supports[j]) & set(supports[i]) for i in reached)}
        if not added:
            return reached == selected
        reached |= added


def finite_support_audit(n, supports, s, p=Fraction(1, 4)):
    families = [selected for t in range(1, min(s, len(supports)) + 1)
                for selected in combinations(range(len(supports)), t)]
    connected_sets = [a for a in families if connected(supports, a)]
    boundaries = {a: boundary(supports, a) for a in families}
    good_by_degree = [0] * (n + 1)
    good_probability = Fraction(0)
    raw_only_traps = []
    checks = 0
    for k in range(n + 1):
        for word in combinations(range(1, n + 1), k):
            variables = frozenset(word)
            bad = any(boundaries[a] <= variables for a in families)
            connected_bad = any(boundaries[a] <= variables for a in connected_sets)
            assert bad == connected_bad
            checks += 1
            if not bad:
                good_by_degree[k] += 1
                good_probability += p**k * (1-p)**(n-k)
            elif not any(set(a) <= variables for a in supports):
                raw_only_traps.append(list(word))
    harris_product = Fraction(1)
    for a in connected_sets:
        harris_product *= 1 - p**len(boundaries[a])
    assert good_probability >= harris_product
    expansion = all(2 * len(boundaries[a]) > len(a) for a in families)
    return dict(variables=n, supports=supports, support_cutoff=s,
                clause_subsets=len(families), connected_clause_subsets=len(connected_sets),
                all_variable_subsets_checked=checks,
                strict_half_boundary_expansion=expansion,
                good_monomials_by_degree=good_by_degree,
                uniform_counts=[comb(n, k) for k in range(n+1)],
                bernoulli_probability=str(good_probability),
                decreasing_event_product=str(harris_product),
                harris_inequality_checked=True,
                raw_clause_only_false_negatives=raw_only_traps)


def parameter_audit(n, epsilon=Fraction(1, 10**16), occurrence=4096):
    # No CNF with n variables is generated.  These are arithmetic hypotheses
    # in an existence theorem for all sufficiently large n.
    C = (3 * occurrence)**2
    p = epsilon / (1024 * C**2)
    mu = p*n
    assert 0 < epsilon <= 1 and mu >= 16
    s = int(epsilon*n)
    R = s // 16
    N = n - R - 1
    loss = 168*n*C**4*p**3
    k_min = (mu.numerator + 2*mu.denominator - 1) // (2*mu.denominator)
    k_max = int(2*mu)
    assert k_min <= k_max
    for k in (k_min, k_max):
        assert 1 <= k <= s // 256
        assert k + 3*R <= s // 4
        assert 3 <= R <= n-1
        assert k <= N and 2*k <= N-k+1
        assert Fraction((R+1)*k, n) - loss >= epsilon*p*n/128
    assert C**2*p <= Fraction(1, 2) and p**3 <= Fraction(1, 2)
    assert loss <= mu/32
    assert mu/8 - loss >= Fraction(3, 2)
    # exp(3/2) > 1 + 3/2 + (3/2)^2/2! + (3/2)^3/3! > 4.
    assert 1 + Fraction(3, 2) + Fraction(9, 8) + Fraction(9, 16) > 4
    return dict(ambient_variables=n, epsilon=str(epsilon), maximum_occurrence=occurrence,
                connected_count_constant=C, bernoulli_p=str(p), expected_set_size=str(mu),
                expansion_cutoff=s, rank_cutoff=R, selected_degree_interval=[k_min, k_max],
                harris_loss_exponent=str(loss),
                distinct_flat_bound_exponent_before_factor_one_quarter=str(epsilon*p*n/128),
                all_rational_budget_checks_passed=True,
                cnf_constructed=False, specific_n_existence_certified=False)


def run():
    fixtures = [
        ('disjoint_triples', 6, [(1, 2, 3), (4, 5, 6)], 12),
        ('linear_triangle', 6, [(1, 2, 3), (3, 4, 5), (1, 5, 6)], 12),
        ('zero_boundary_pasch', 6, [(1, 2, 3), (1, 4, 5), (2, 4, 6), (3, 5, 6)], 12),
    ]
    cases = [dict(name=name, **finite_support_audit(n, f, s)) for name,n,f,s in fixtures]
    assert cases[0]['good_monomials_by_degree'] == [1, 6, 15, 18, 9, 0, 0]
    assert [2, 4, 6] in cases[1]['raw_clause_only_false_negatives']
    assert not cases[2]['strict_half_boundary_expansion']
    assert not any(cases[2]['good_monomials_by_degree'])
    parameters = [parameter_audit(10**power) for power in (40, 60, 80)]
    return dict(schema_version=1, all_checks_passed=True, cases=cases, parameters=parameters,
                summary=dict(finite_support_families=len(cases),
                             exhaustive_variable_subsets=sum(c['all_variable_subsets_checked'] for c in cases),
                             rational_parameter_checks=len(parameters),
                             connected_component_reduction_checked=True,
                             harris_product_checked=True,
                             source_clause_only_test_counterexample=True,
                             failed_expansion_control_detected=True),
                scope='Exact finite combinatorics and rational parameter budgets. These do not generate the asymptotic hard family, determine an explicit existence threshold, or establish the general lower bound by experiment; see the mathematical proofs.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out / 'expander_separation.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(report['summary'])
