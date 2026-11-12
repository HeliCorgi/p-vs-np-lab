#!/usr/bin/env python3
"""Audit pre-generation region cuts, quotient refinement, and their full cost."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT))

from experiments.mcsp_counterexample_search import CASES, semantic_catalog
from pnp_lab.mcsp_counterexample import witness_table
from pnp_lab.mcsp_region_search import search_regions, solve_samples


def audit(baseline):
    # Chosen before the panel: same 288 cases as the previous search experiment.
    modes = {'quotient': 0, 'quotient_and_regions': 128}
    suffix_counts = Counter()
    certificates, certificate_ids = [], {}

    @lru_cache(maxsize=65536)
    def suffix_exists(wires, target, width, remaining):
        # Independently enumerate literal straight-line suffixes. In particular,
        # keep redundant wires and do not use the solver's depth relaxation.
        suffix_counts['calls'] += 1
        if target in wires:
            return True
        if remaining == 0:
            return False
        outputs = [(1 << width) - 1 ^ a for a in wires]
        for a, b in combinations_with_replacement(wires, 2):
            outputs.extend((a & b, a | b))
        for value in outputs:
            suffix_counts['gate_operations'] += 1
            if suffix_exists((*wires, value), target, width, remaining - 1):
                return True
        return False

    assert [(g['n'], g['gate_budget']) for g in baseline['groups']] == list(CASES)
    groups, cut_checks, candidate_checks = [], 0, 0
    for old_group, (n, budget) in zip(baseline['groups'], CASES):
        feasible = semantic_catalog(n, budget)
        totals = {mode: Counter() for mode in modes}
        old_totals, comparisons, cases = Counter(), Counter(), []
        for table in range(1 << (1 << n)):
            old = old_group['cases'][table]
            assert old['target'] == table
            runs = {mode: search_regions(n, budget, table, relaxation_limit=cap)
                    for mode, cap in modes.items()}
            for mode, result in runs.items():
                assert (result['status'] == 'YES') == (table in feasible)
                assert result['status'] == old['status']
                if result['witness']:
                    assert witness_table(result['witness']) == table
                    assert len(result['witness']['gates']) <= budget
                for iteration in result['iterations']:
                    if iteration['witness']:
                        candidate = witness_table(iteration['witness'])
                        assert all(candidate >> row & 1 == bit for row, bit in iteration['examples'])
                        candidate_checks += 1
                    for cut in iteration['pruned_regions']:
                        assert not suffix_exists(tuple(cut['available']), iteration['target_signature'],
                                                 iteration['sample_count'], cut['remaining'])
                        cut_checks += 1
                    # Share identical audit certificates in the saved report.
                    # This happens after the run and never assists the search.
                    refs = []
                    for cut in iteration['pruned_regions']:
                        record = dict(cut, width=iteration['sample_count'],
                                      target=iteration['target_signature'])
                        key = json.dumps(record, sort_keys=True)
                        if key not in certificate_ids:
                            certificate_ids[key] = len(certificates)
                            certificates.append(record)
                        refs.append(certificate_ids[key])
                    iteration['pruned_region_certificate_ids'] = refs
                    del iteration['pruned_regions']
                    assert iteration['examples'] == result['examples'][:iteration['sample_count']]
                    del iteration['examples']  # Recover as a prefix of the run's final examples.
                    del iteration['complete_sample_decision']
                    iteration['metrics'] = {key: iteration['metrics'][key] for key in (
                        'states_created', 'transition_attempts', 'infeasible_region_cuts',
                        'relax_gate_ops', 'relax_unknown', 'work_units')}
                del result['no_scope']
                for key, value in result['metrics'].items():
                    if key.startswith('peak_'):
                        totals[mode][key] = max(totals[mode][key], value)
                    else:
                        totals[mode][key] += value
            change = runs['quotient_and_regions']['metrics']['work_units'] - runs['quotient']['metrics']['work_units']
            comparisons['region_work_' + ('lower' if change < 0 else 'higher' if change > 0 else 'equal')] += 1
            change = (runs['quotient_and_regions']['metrics']['states_created']
                      - runs['quotient']['metrics']['states_created'])
            comparisons['region_states_' + ('lower' if change < 0 else 'higher' if change > 0 else 'equal')] += 1
            old_metrics = old['metrics']['lazy_samples_and_gates']
            previous = {'transition_attempts': old['lazy_construction']['transition_attempts'],
                        'candidate_roots_created': old['lazy_construction']['candidate_roots'],
                        'state_records_created': old['lazy_construction']['state_records_created'],
                        'candidate_visits': old_metrics['candidate_visits'],
                        'cold_accounted_work_units': old_metrics['work_units']
                        + old['construction_event_units']['lazy_samples_and_gates']}
            old_totals.update(previous)
            cases.append({'target': table, 'status': old['status'], 'previous_lazy_search': previous,
                          'runs': runs})
        groups.append({'n': n, 'gate_budget': budget, 'truth_tables': len(cases),
                       'feasible_functions': len(feasible), 'previous_lazy_totals': dict(old_totals),
                       'totals': {mode: dict(value) for mode, value in totals.items()},
                       'comparison_within_new_cost_model': dict(comparisons), 'cases': cases})

    root = solve_samples(2, 2, [(row, 6 >> row & 1) for row in range(4)])
    assert root['status'] == 'NO' and root['metrics']['transition_attempts'] == 0
    assert root['metrics']['relax_gate_ops'] == 104
    # Literal syntax uses unordered AND/OR parent pairs, permits redundant
    # gates, and selects ANY available wire as output for each length.
    descriptions, prefixes = 4, 1
    for depth in (1, 2):
        wires = 4 + depth - 1
        prefixes *= wires * (wires + 2)
        descriptions += prefixes * (wires + 1)
    assert descriptions == 5164
    return {'schema_version': 1, 'all_checks_passed': True, 'truth_tables': 288, 'searches': 576,
            'case_selection': 'All tables for (n,s)=(2,2),(2,4),(3,3), unchanged from the previous audit.',
            'scope': 'Sound finite sample-state pruning; no general polynomial bound or P vs NP conclusion.',
            'cost_model': 'New work units include signature bit widths, generated states, every refinement rebuild, '
                          'bounded relaxation and full verification. They are logical accounting events, not exact '
                          'bit operations or time. Only the two new variants use the same ledger; the old search '
                          'ledger is reported separately and is not a speedup denominator.',
            'relaxation_limit_per_state': 128, 'candidate_witnesses_checked': candidate_checks,
            'iteration_encoding': 'Round examples are the first sample_count entries of the run examples. '
                                  'Round ledgers are abbreviated; aggregate run ledgers include every metric. '
                                  'Certificate IDs index region_certificates and are assigned only after search.',
            'pruned_regions_independently_checked': cut_checks,
            'region_certificates': certificates,
            'independent_suffix_audit': dict(suffix_counts),
            'root_exclusion_example': {'n': 2, 'gate_budget': 2, 'target': 6,
                                       'literal_descriptions_excluded': descriptions, 'result': root},
            'groups': groups}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=Path('results'))
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    previous = args.out_dir / 'mcsp_counterexample_search.json'
    if not previous.exists():
        previous = Path(__file__).resolve().parents[1] / 'results/mcsp_counterexample_search.json'
    result = audit(json.loads(previous.read_text()))
    (args.out_dir / 'mcsp_region_pruning.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: result[key] for key in ('all_checks_passed', 'truth_tables', 'searches',
                       'candidate_witnesses_checked', 'pruned_regions_independently_checked')}, sort_keys=True))


if __name__ == '__main__':
    main()
