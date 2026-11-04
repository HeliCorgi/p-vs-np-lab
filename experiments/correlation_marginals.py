"""Replay compact level-four SA witnesses on the original SAT/UNSAT twins."""
import argparse
import json
from pathlib import Path

from pnp_lab.local_marginals import check_local_marginals, linear_triple_marginals
from pnp_lab.modular_barrier import check_preorder, line_fixture


def run():
    n, raw = line_fixture(0)
    raw = raw[:152]
    old = json.loads((Path(__file__).resolve().parents[1]
                      / 'results/modular_barrier.json').read_text())
    assert check_preorder(n, raw, old['fixture']['tree_preorder'])
    positive = tuple(tuple(map(abs, c)) for c in raw)
    all_true = (1 << n) - 1
    assert all(any(bool(all_true >> (abs(l) - 1) & 1) == (l > 0) for l in c)
               for c in positive)
    cases = []
    for label, cs in (('original_unsat', raw), ('all_positive_sat', positive)):
        out = linear_triple_marginals(n, cs)
        assert out['status'] == 'UNKNOWN' and out['relaxation'] == 'FEASIBLE'
        assert check_local_marginals(n, cs, out['certificate'])
        cases.append(dict(label=label, variables=n, clauses=len(cs),
                          certificate=out['certificate'], stats=out['stats'],
                          decision_status=out['status'], relaxation=out['relaxation'],
                          independently_checked=True))
    overlapping = linear_triple_marginals(4, [(1, 2, 3), (-1, -2, 4)])
    capped = linear_triple_marginals(n, raw, max_states=0)
    assert overlapping['relaxation'] == 'UNKNOWN' and overlapping['certificate'] is None
    assert capped['relaxation'] == 'UNKNOWN' and capped['stats']['budget_limited']
    return dict(schema_version=1, all_checks_passed=True, cases=cases,
                controls=dict(overlapping_triples=overlapping, exhausted_cap=capped),
                summary=dict(checked_twins=2, level=4,
                             scopes_per_case=36457, states_per_case=541323,
                             positive_states_per_case=506667,
                             projection_equalities_per_case=1062711,
                             original_unsat_certificate_checked=True,
                             positive_model_checked=True),
                scope='Feasible level-four local distributions, not SAT models. The exact level-five upper bound on the UNSAT twin follows from the separately checked join/project refutation, not from an LP solver execution. The mathematical level convention is specified in docs/correlation_proof_boundary.md.')


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--out-dir', type=Path, required=True)
    outdir = cli.parse_args().out_dir
    outdir.mkdir(parents=True, exist_ok=True)
    result = run()
    (outdir / 'correlation_marginals.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(result['summary'])
