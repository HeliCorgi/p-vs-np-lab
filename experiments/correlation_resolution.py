"""Exact finite proof-width comparison on the previous integer-blind fixture."""
import argparse
import hashlib
import json
from pathlib import Path

from pnp_lab.integer_hull import integer_hull_refute
from pnp_lab.modular_barrier import check_preorder, line_fixture
from pnp_lab.resolution_closure import (
    check_resolution, check_width_closure, replay_resolution, resolution_refute)
from pnp_lab.ternary_flow import scramble


def holds(cs, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in cs)


def saved_tree_baseline(n, cs):
    """Convert an existing proof for comparison; discovery never calls this."""
    source = Path(__file__).resolve().parents[1]/'results/modular_barrier.json'
    data = json.loads(source.read_text())
    tokens = data['fixture']['tree_preorder']
    assert check_preorder(n, cs, tokens)
    rows = [frozenset(c) for c in cs]
    nodes = [dict(op='input', clause=i) for i in range(len(cs))]
    known = {c: i for i, c in enumerate(rows)}
    next_token = iter(tokens)

    def visit():
        token = next(next_token)
        if token >= 0:
            return token
        v = -token
        a, b = visit(), visit()
        left, right = rows[a], rows[b]
        if v not in left:
            return a
        if -v not in right:
            return b
        r = (left - {v}) | (right - {-v})
        assert not any(-l in r for l in r)
        if r not in known:
            known[r] = len(rows)
            rows.append(r)
            nodes.append(dict(op='resolve', left=a, right=b, pivot=v))
        return known[r]

    root = visit()
    assert not rows[root]
    assert next(next_token, None) is None
    needed, pending = set(), [root]
    while pending:
        i = pending.pop()
        if i in needed:
            continue
        needed.add(i)
        t = nodes[i]
        if t['op'] == 'resolve':
            pending.extend((t['left'], t['right']))
    order = sorted(needed)
    rename = {old: new for new, old in enumerate(order)}
    pruned = []
    for old in order:
        t = dict(nodes[old])
        if t['op'] == 'resolve':
            t['left'], t['right'] = rename[t['left']], rename[t['right']]
        pruned.append(t)
    cert = dict(kind='boolean-resolution-v1', nodes=pruned, root=rename[root],
                width=max(len(rows[i]) for i in order))
    assert check_resolution(n, cs, cert)
    return dict(source='results/modular_barrier.json',
                tree_sha256=hashlib.sha256(json.dumps(tokens, separators=(',', ':')).encode()).hexdigest(),
                tree_nodes=len(tokens), converted_nodes=len(pruned),
                converted_inputs=sum(t['op'] == 'input' for t in pruned),
                converted_resolutions=sum(t['op'] == 'resolve' for t in pruned),
                converted_width=cert['width'], independently_checked=True)


def run():
    n, raw = line_fixture(0)
    raw = raw[:152]
    positive = tuple(tuple(map(abs, c)) for c in raw)
    all_true = (1 << n)-1
    assert holds(positive, all_true)
    # A necessary integer relaxation is silent on this same original input.
    integer = integer_hull_refute(n, raw)
    assert integer['status'] == 'UNKNOWN'
    assert integer['stats']['scope_complete'] and integer['stats']['local_rows'] == 0
    baseline = saved_tree_baseline(n, raw)
    cases = []
    sample = None
    closure = None
    for seed in (None, 16001, 16002, 16003):
        for bad in (True, False):
            cs = raw if bad else positive
            word = None if bad else all_true
            if seed is not None:
                cs, word = scramble(n, cs, word, seed)
            if word is not None:
                assert holds(cs, word)
            lower = resolution_refute(n, cs, width=3)
            assert lower['status'] == 'UNKNOWN' and lower['stats']['complete']
            assert not lower['stats']['budget_limited']
            assert check_width_closure(n, cs, lower['closure_certificate'])
            upper = resolution_refute(n, cs, width=4)
            assert upper['status'] == ('UNSAT' if bad else 'UNKNOWN')
            if bad:
                assert check_resolution(n, cs, upper['certificate'])
                rechecked = replay_resolution(n, cs, upper['certificate'])
                assert max(map(len, rechecked)) == 4
                assert upper['stats']['certificate_parent_union_width'] == 5
                if seed is None:
                    sample = dict(variables=n, clauses=cs, certificate=upper['certificate'])
                    closure = lower['closure_certificate']
            else:
                assert upper['stats']['complete'] and check_width_closure(
                    n, cs, upper['closure_certificate'])
                assert word is not None
            cases.append(dict(scramble_seed=seed, unsatisfiable=bad, variables=n,
                              clauses=len(cs), sat_word_checked=word is not None,
                              width_three=lower['stats'], width_four=upper['stats'],
                              status=upper['status']))
    first = cases[0]['width_four']
    assert first['certificate_nodes'] == 368 and first['certificate_inputs'] == 115
    assert first['first_retained_derived_by_width']['2']['raw_ancestors'] == 13
    assert first['first_retained_derived_by_width']['1']['raw_ancestors'] == 41
    return dict(schema_version=1, all_checks_passed=True, cases=cases,
                saved_tree_baseline=baseline,
                sample_refutation=sample, sample_width_three_closure=closure,
                integer_baseline=dict(status=integer['status'], local_rows=0,
                                      profiled_scopes=integer['stats']['scopes_profiled']),
                summary=dict(inputs=len(cases), checked_refutations=4,
                             checked_sat_controls=4, variables=n, clauses=len(raw),
                             exact_minimum_resolution_width=4,
                             maximum_parent_union=5,
                             original_search_rows=first['stored_rows'],
                             original_search_pairs=first['pairs_checked'],
                             original_search_subsumption_probes=first['subsumption_probes'],
                             original_proof_nodes=first['certificate_nodes'],
                             original_proof_inputs=first['certificate_inputs'],
                             original_proof_resolutions=first['certificate_resolutions'],
                             original_proof_bytes=first['certificate_bytes'],
                             first_retained_binary_raw_ancestors=13,
                             first_retained_unit_raw_ancestors=41,
                             saved_tree_converted_width=baseline['converted_width']),
                scope='An exact finite width-4 ordinary-resolution result, with independent width-3 closure obstruction. The finder uses no saved proof or construction metadata. Known unbounded resolution-width lower bounds still apply to other families; no general SAT polynomial-time claim.')


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--out-dir', type=Path, required=True)
    out = cli.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    r = run()
    (out/'correlation_resolution.json').write_text(json.dumps(r, sort_keys=True, indent=2)+'\n')
    print(r['summary'])

