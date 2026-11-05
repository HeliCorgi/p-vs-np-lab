"""Finite audit of prime-power digits of checked weighted integer refutations.

No symbolic algebra package, floating arithmetic or polynomial-calculus proof
finder is used. Polynomial monomials use Boolean quotient multiplication.
This reports identities on the named instances, not a PC derivation.
"""
import argparse
from copy import deepcopy
import json
from math import comb
from pathlib import Path

from pnp_lab.integer_hull import check_integer_hull
from pnp_lab.one_column_feedback import one_column_certificate
if __package__:
    from .feedback_prime_power import carry_ring
else:
    from feedback_prime_power import carry_ring


def binomial_digit(exponent, j, p):
    if exponent < 0:
        return ((-1)**j * comb(j-exponent-1, j)) % p
    return (comb(exponent, j) if j <= exponent else 0) % p


def series_mul(a, b, p):
    return tuple(sum(a[i]*b[j-i] for i in range(j+1)) % p for j in range(len(a)))


def unit_power(exponent, D, p):
    """Integer power by squaring, in F_p[z]/(z^(D+1))."""
    base = (1, 1) + (0,)*(D-1)
    ans = (1,) + (0,)*D
    if exponent < 0:
        # Solve base * inv = 1 coefficient by coefficient.
        inv = [1]
        for j in range(1, D+1):
            inv.append(-sum(base[k]*inv[j-k] for k in range(1, j+1)) % p)
        assert series_mul(base, inv, p) == ans
        base = tuple(inv)
        exponent = -exponent
    while exponent:
        if exponent & 1:
            ans = series_mul(ans, base, p)
        base = series_mul(base, base, p)
        exponent >>= 1
    return ans


def local_coefficients(scope, table, j, p):
    """Möbius inversion on a Boolean cube; no degree assumption in conversion."""
    values = [t[j] for t in table]
    for i in range(len(scope)):
        for w in range(len(values)):
            if w >> i & 1:
                values[w] = (values[w] - values[w ^ (1 << i)]) % p
    a = {}
    for w, v in enumerate(values):
        if v:
            mon = sum(1 << (k-1) for i, k in enumerate(scope) if w >> i & 1)
            a[mon] = v
    return a


def evaluate(poly, word, p):
    return sum(v for m, v in poly.items() if (m & word) == m) % p


def audit(n, core, cert, p, D, *, max_products=2000000):
    """A bounded finite verification; UNKNOWN only means the audit did not finish."""
    if type(max_products) is not int or max_products < 0:
        raise ValueError('invalid sparse product cap')
    if not (1 <= n <= 26 and p in (2, 3, 5) and 1 <= D <= 5):
        raise ValueError('outside the size and characteristic of this finite audit')
    if not check_integer_hull(n, core, cert):
        raise ValueError('integer certificate failed independent replay')
    m = cert['modulus']
    raw_rhs = sum(t['weight']*t['rhs'] for t in cert['terms'])
    raw_mod = raw_rhs % m
    assert raw_mod and m % (D*p) == 0
    first = 1
    while raw_mod % (first*p) == 0:
        first *= p
    assert first == D
    stats = dict(local_words=0, positive_model_cells=0, negative_exponent_cells=0,
                 modular_model_cells_with_nonzero_exponent=0, sparse_products=0,
                 peak_live_coefficient_terms=1, local_degrees=[0]*(D+1),
                 peak_prefix_degrees=[0]*(D+1), global_truth_assignments=0)
    running = [{0:1}] + [{} for _ in range(D)]
    totals = [0]*n
    for term in cert['terms']:
        scope = term['scope']
        assert len(scope) <= 3
        table = []
        for bits in range(1 << len(scope)):
            one = sum(((bits >> i) & 1) << (v-1) for i,v in enumerate(scope))
            loc = term['weight'] * (sum(a for i,a in enumerate(term['coeff']) if bits >> i & 1) - term['rhs'])
            coeffs = unit_power(loc, D, p)
            assert coeffs == tuple(binomial_digit(loc,j,p) for j in range(D+1))
            stats['local_words'] += 1
            stats['negative_exponent_cells'] += loc < 0
            if all(any(bool(one >> (abs(l)-1) & 1) == (l > 0) for l in core[ix]) for ix in term['clauses']):
                stats['positive_model_cells'] += 1
                assert coeffs == (1,) + (0,)*D
                if term['modulus'] and loc:
                    stats['modular_model_cells_with_nonzero_exponent'] += 1
            table.append(coeffs)
        local = [local_coefficients(scope, table, j, p) for j in range(D+1)]
        for j, poly in enumerate(local):
            degree = max((u.bit_count() for u in poly), default=0)
            assert degree <= j
            stats['local_degrees'][j] = max(stats['local_degrees'][j], degree)
            for w, t in enumerate(table):
                assignment = sum(1 << (k-1) for i,k in enumerate(scope) if w >> i & 1)
                assert evaluate(poly, assignment, p) == t[j]
        for v,a in zip(scope, term['coeff']):
            totals[v-1] += term['weight']*a
        out = [{} for _ in range(D+1)]
        for i, left in enumerate(running):
            for j, right in enumerate(local[:D-i+1]):
                tgt = out[i+j]
                for u,a in left.items():
                    for v,b in right.items():
                        if stats['sparse_products'] >= max_products:
                            return dict(status='UNKNOWN', reason='sparse product cap', stats=stats)
                        stats['sparse_products'] += 1
                        mon = u | v  # x_i² = x_i
                        c = (tgt.get(mon, 0) + a*b) % p
                        if c:
                            tgt[mon] = c
                        else:
                            tgt.pop(mon, None)
        running = out
        for j, poly in enumerate(running):
            degree = max((u.bit_count() for u in poly), default=0)
            assert degree <= j
            stats['peak_prefix_degrees'][j] = max(stats['peak_prefix_degrees'][j], degree)
        stats['peak_live_coefficient_terms'] = max(stats['peak_live_coefficient_terms'],
                                                    sum(map(len,running)))
    assert all(a % m == 0 for a in totals)
    expected = [binomial_digit(-raw_rhs, j, p) for j in range(D+1)]
    assert expected[0] == 1 and not any(expected[1:D]) and expected[D] != 0
    assert running == [({0:v} if v else {}) for v in expected]
    # Independent full-assignment check only on small ambient cores. The
    # sparse global polynomial check above includes *all* 26-variable cases.
    if n <= 10:
        for x in range(1 << n):
            exponent = -raw_rhs + sum(a for i,a in enumerate(totals) if x >> i & 1)
            assert unit_power(exponent,D,p) == tuple(expected)
            stats['global_truth_assignments'] += 1
    return dict(status='VERIFIED', modulus=m, characteristic=p, first_detecting_degree=D,
                residual_rhs_mod_m=raw_mod, global_series_coefficients=expected,
                variables=n, terms=len(cert['terms']), product_cap=max_products, stats=stats)


def run():
    cases = []
    capped = None
    for m, charge, p, D in ((4,2,2,2), (8,4,2,4), (9,3,3,3), (25,5,5,5)):
        n, rows, _ = carry_ring(m,charge)
        for sign_flip in (False,True):
            cs = tuple(tuple(-l if sign_flip and (abs(l) % 2 or abs(l)==n) else l
                             for l in c) for c in rows)
            cert, _ = one_column_certificate(n, cs)
            assert cert and cert['modulus'] == m
            if sign_flip:
                # Redundant, explicit congruence stress term: p*x == 0 mod p.
                # It contributes -m*x to the exponent. It has nonzero
                # exponent on a satisfying local word yet zero lower digits.
                cert = deepcopy(cert)
                cert['terms'].append(dict(scope=[1], clauses=[], coeff=[p], rhs=0,
                                          modulus=p, weight=-(m//p)))
            a = audit(n, cs, cert, p, D)
            assert a['status'] == 'VERIFIED' and a['stats']['negative_exponent_cells'] > 0
            assert a['stats']['modular_model_cells_with_nonzero_exponent'] == int(sign_flip)
            a.update(sign_flip=sign_flip, redundant_congruence_stress_term=sign_flip,
                     source_charge=charge)
            cases.append(a)
            if capped is None:
                capped = audit(n, cs, cert, p, D, max_products=0)
                assert capped['status'] == 'UNKNOWN'
    return dict(schema_version=1, all_checks_passed=True, cases=cases,
                capped_control=capped, summary=dict(
                    verified_integer_certificates=len(cases), tested_moduli=[4,8,9,25],
                    first_detecting_degrees=[2,4,3,5], sparse_global_identities=len(cases),
                    full_truth_assignments=sum(a['stats']['global_truth_assignments'] for a in cases),
                    local_words=sum(a['stats']['local_words'] for a in cases),
                    symbolic_products=sum(a['stats']['sparse_products'] for a in cases),
                    largest_variables=max(a['variables'] for a in cases)),
                scope='Truncated series and square-free Boolean polynomial identities for the stated checked carry certificates, not a proof-system checker or all-input SAT solver. Original 26-variable cubes are not enumerated; the full sparse coefficient products are compared symbolically.')


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--out-dir', type=Path, required=True)
    out = cli.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    r = run()
    (out/'feedback_digits.json').write_text(json.dumps(r, sort_keys=True, indent=2)+'\n')
    print(r['summary'])
