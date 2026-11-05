"""Recover a composite modulus through one-way shields on raw ternary clauses."""
import argparse
import json
from pathlib import Path

from pnp_lab.feedback_fixture import shield_clauses
from pnp_lab.integer_feedback import integer_feedback_refute, check_integer_feedback
from pnp_lab.integer_hull import integer_hull_refute
from pnp_lab.ternary_flow import scramble


def carry_ring(m, q):
    """Exact table of a_i + x - a_(i+1) = c_i, using only proper ternary clauses."""
    if type(m) is not int or m < 3 or type(q) is not int or not 0 <= q <= m:
        raise ValueError('invalid cycle')
    rows = []
    x = m + 1
    for i in range(m):
        vs = (i+1, x, (i+1) % m+1)
        charge = (i+1)*q//m - i*q//m
        bad = [w for w in range(8)
               if (w & 1) + ((w >> 1) & 1) - ((w >> 2) & 1) != charge]
        assert len(bad) == 5
        for j, w in enumerate(bad):
            c = tuple(-v if w >> k & 1 else v for k, v in enumerate(vs))
            head = j % 3
            rows.append(c[:head] + c[head+1:] + (c[head],))
    return x, tuple(rows), (0 if q == 0 else 1 << m if q == m else None)


def holds(cs, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs)


def run():
    cases = []
    for m, q in ((4, 2), (9, 3), (25, 5), (8, 4), (4, 0)):
        n, core, word = carry_ring(m, q)
        N, raw, lifted = shield_clauses(n, core, layers=16, word=word)
        cs, truth = scramble(N, raw, lifted, 17400 + m)
        if truth is not None:
            assert holds(cs, truth)
        raw_baseline = None
        if m == 4 and q == 2:
            baseline = integer_hull_refute(N, cs)
            assert baseline['status'] == 'UNKNOWN' and baseline['stats']['scope_complete']
            assert baseline['stats']['local_rows'] == 0
            raw_baseline = dict(scopes=baseline['stats']['scopes_profiled'], rows=0)
        ans = integer_feedback_refute(N, cs)
        stats = ans['stats']
        assert stats['learned_clauses'] == 5*m
        case = dict(gates=m, total=q, variables=N, clauses=len(cs), anchors=stats['anchors'],
                    learned_clauses=stats['learned_clauses'], path_steps=stats['path_steps'],
                    edges_visited=stats['edges_visited'], status=ans['status'],
                    raw_integer_baseline=raw_baseline, raw_sat_word_checked=truth is not None)
        if truth is None:
            assert ans['status'] == 'UNSAT' and stats['backend'] == 'signed_column'
            assert check_integer_feedback(N, cs, ans['certificate'])
            proof = stats['signed_column']
            assert proof['modulus'] == m and proof['certificate_terms'] == m
            case.update(backend=stats['backend'], modulus=m, arithmetic=proof,
                        certificate_bytes=len(json.dumps(ans['certificate'],sort_keys=True,separators=(',',':')).encode()))
        else:
            assert ans['status'] == 'UNKNOWN'
        cases.append(case)
    return dict(all_checks_passed=True, cases=cases,
                summary=dict(inputs=len(cases), checked_composite_refutations=4,
                             recovered_moduli=[c['modulus'] for c in cases if 'modulus' in c],
                             satisfiable_controls=1, max_variables=max(c['variables'] for c in cases)),
                scope='The field comparison concerns affine equations over unrestricted field-valued coordinates. No lower bound on resolution for the carry ring is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out/'feedback_prime_power.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(report['summary'])
