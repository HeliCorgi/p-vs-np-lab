#!/usr/bin/env python3
"""Exhaustive finite comparison of counterexamples and shared gate-value reuse."""

import argparse
from collections import Counter
from itertools import combinations_with_replacement
import json
from pathlib import Path

from pnp_lab.mcsp_counterexample import build_catalog, search, search_lazy, witness_table


# Fixed before evaluating the search variants; every truth table is included.
CASES = ((2, 2), (2, 4), (3, 3))
EAGER_MODES = ('fresh', 'samples', 'samples_and_gates')
MODES = (*EAGER_MODES, 'lazy_samples_and_gates')


def construction_units(ledger):
    return (ledger['transition_attempts'] + ledger['state_insert_attempts']
            + ledger['candidate_roots'] + ledger['state_records_created'])


def semantic_catalog(n, budget):
    """Independent feasibility oracle; never used by the synthesis algorithm."""
    mask = (1 << (1 << n)) - 1
    base = frozenset({0, mask} | {
        sum(((x >> (n - 1 - i)) & 1) << x for x in range(1 << n))
        for i in range(n)})
    states, functions = {base}, set(base)
    for _ in range(budget):
        following = set()
        for state in states:
            possible = {mask ^ a for a in state}
            for a, b in combinations_with_replacement(sorted(state), 2):
                possible.update((a & b, a | b))
            for value in possible - state:
                following.add(state | {value})
                functions.add(value)
        states = following
    return functions


def audit():
    groups = []
    for n, budget in CASES:
        catalog = build_catalog(n, budget)
        feasible = semantic_catalog(n, budget)
        # Validate the entire generated representation independently of search.
        tables = {witness_table(catalog.witness(root)) for root in range(len(catalog.nodes))}
        assert tables == feasible
        construction = catalog.construction
        construction_events = construction_units(construction)
        totals = {mode: Counter() for mode in MODES}
        comparison = Counter()
        rows = []
        for target in range(1 << (1 << n)):
            runs = {mode: search(catalog, target, mode) for mode in EAGER_MODES}
            lazy_catalog, runs['lazy_samples_and_gates'] = search_lazy(n, budget, target)
            generation = {mode: construction_events for mode in EAGER_MODES}
            generation['lazy_samples_and_gates'] = construction_units(lazy_catalog.construction)
            assert generation['lazy_samples_and_gates'] <= construction_events
            assert runs['lazy_samples_and_gates'] == runs['samples_and_gates']
            if runs['lazy_samples_and_gates']['status'] == 'NO':
                assert lazy_catalog.construction['complete']
            assert len({result['root'] for result in runs.values()}) == 1
            for mode, result in runs.items():
                assert (result['status'] == 'YES') == (target in feasible)
                if result['witness'] is not None:
                    assert witness_table(result['witness']) == target
                    assert len(result['witness']['gates']) <= budget
                metrics = result['metrics']
                totals[mode].update({k: v for k, v in metrics.items() if k != 'peak_value_cache'})
                totals[mode]['peak_value_cache'] = max(totals[mode]['peak_value_cache'],
                                                     metrics['peak_value_cache'])
                totals[mode]['construction_event_units'] += generation[mode]
                totals[mode]['cold_accounted_work_units'] += metrics['work_units'] + generation[mode]
            samples = runs['samples']['metrics']
            shared = runs['samples_and_gates']['metrics']
            assert runs['samples']['counterexample_rows'] == runs['samples_and_gates']['counterexample_rows']
            assert samples['row_root_checks'] == shared['row_root_checks']
            assert shared['gate_evaluations'] <= samples['gate_evaluations']
            assert shared['work_units'] <= samples['work_units']
            for mode in MODES[1:]:
                change = runs[mode]['metrics']['work_units'] - runs['fresh']['metrics']['work_units']
                comparison[mode + ('_better' if change < 0 else '_worse' if change > 0 else '_equal')] += 1
                cold_change = change + generation[mode] - generation['fresh']
                comparison[mode + ('_cold_better' if cold_change < 0 else '_cold_worse' if cold_change > 0
                                   else '_cold_equal')] += 1
            rows.append({'target': target, 'status': runs['fresh']['status'],
                         'witness': runs['fresh']['witness'],
                         'counterexample_rows': runs['samples']['counterexample_rows'],
                         'construction_event_units': generation,
                         'lazy_construction': lazy_catalog.construction,
                         'metrics': {mode: runs[mode]['metrics'] for mode in MODES}})
        groups.append({'n': n, 'gate_budget': budget, 'truth_tables': len(rows),
                       'feasible_functions': len(feasible), 'construction': construction,
                       'construction_event_units': construction_events,
                       'totals': {mode: dict(value) for mode, value in totals.items()},
                       'comparison_to_fresh': dict(comparison), 'cases': rows})
    return {'schema_version': 1, 'all_checks_passed': True,
            'scope': 'Finite complete catalogues, not polynomial-time general MCSP or P vs NP evidence.',
            'cost_model': 'Logical event counters, not wall-clock time or exact bit operations. '
                          'Cold totals charge actual generation per target, including full enumeration for eager modes; '
                          'no preprocessing advice is free.',
            'case_selection': 'Every truth table for (n,s)=(2,2),(2,4),(3,3); fixed candidate and query orders.',
            'truth_tables': sum(group['truth_tables'] for group in groups),
            'searches': len(MODES) * sum(group['truth_tables'] for group in groups), 'groups': groups}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=Path('results'))
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    result = audit()
    (args.out_dir / 'mcsp_counterexample_search.json').write_text(
        json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'all_checks_passed': True, 'truth_tables': result['truth_tables'],
                      'searches': result['searches'],
                      'comparisons': [g['comparison_to_fresh'] for g in result['groups']]}, sort_keys=True))


if __name__ == '__main__':
    main()
