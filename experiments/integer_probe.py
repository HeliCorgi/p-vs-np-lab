"""Conditional integer certificates on a raw CNF disjunction of two flow arms."""
import argparse
import json
from pathlib import Path

from pnp_lab.integer_hull import integer_hull_refute
from pnp_lab.integer_probe import (integer_probe_refute, check_integer_probe,
                                   guarded_disjunction)
from pnp_lab.ternary_flow import prism_flow, scramble


def run():
    cases = []
    sample = None
    for k in (4, 7, 12):
        for bad_left, bad_right in ((True, True), (False, True), (True, False)):
            n, f, fw = prism_flow(k, bad=bad_left, modulus=2)
            m, g, gw = prism_flow(k, bad=bad_right)
            v, cs, word, _ = guarded_disjunction(n, f, m, g, left_word=fw, right_word=gw)
            raw, word = scramble(v, cs, word, 15015 + k)
            if word is not None:
                assert all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in raw)
            root = integer_hull_refute(v, raw)
            assert root['status'] == 'UNKNOWN' and root['stats']['scope_complete']
            assert root['stats']['local_rows'] == 0
            q = integer_probe_refute(v, raw, max_calls=6)
            bad = bad_left and bad_right
            assert q['status'] == ('UNSAT' if bad else 'UNKNOWN')
            if bad:
                assert check_integer_probe(v, raw, q['certificate'])
                assert q['stats']['integer_calls'] == 3 and q['stats']['learned_units'] == 1
                assert set(q['stats']['certificate_moduli']) == {2, 3}
                if k == 4:
                    sample = dict(variables=v, clauses=raw, certificate=q['certificate'])
            capped = integer_probe_refute(v, raw, max_calls=1)
            assert capped['status'] == 'UNKNOWN' and capped['stats']['budget_limited']
            cases.append(dict(k=k, variables=v, clauses=len(raw), bad_left=bad_left,
                              bad_right=bad_right, raw_sat_word_checked=word is not None,
                              initial_local_scopes=root['stats']['scopes_profiled'],
                              initial_integer_rows=0, status=q['status'],
                              stats=q['stats']))
    return dict(schema_version=1, all_checks_passed=True, cases=cases,
                sample_refutation=sample,
                summary=dict(cases=len(cases), checked_refutations=sum(c['status']=='UNSAT' for c in cases),
                             checked_sat_controls=sum(c['raw_sat_word_checked'] for c in cases),
                             largest_variables=max(c['variables'] for c in cases),
                             largest_clauses=max(c['clauses'] for c in cases),
                             refutation_oracle_calls=3, learned_units_per_refutation=1),
                scope='Known failed-value inference with a new certified integer oracle; a simple guarded-flow control, not a reconstruction of the Lichter-Pago hierarchy lower bound. General SAT remains unresolved.')


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--out-dir', type=Path, required=True)
    out = cli.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    r = run()
    (out/'integer_probe.json').write_text(json.dumps(r, sort_keys=True, indent=2) + '\n')
    print(r['summary'])
