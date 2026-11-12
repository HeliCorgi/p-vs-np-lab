#!/usr/bin/env python3
"""Charge construction, normalization, decomposition and exact residual reuse."""

import argparse
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT))

from experiments.mcsp_counterexample_search import CASES, semantic_catalog
from pnp_lab.cnf_component_cache import ComponentSolver, search_shared
from pnp_lab.mcsp_counterexample import witness_table


WORK_CAP = 500_000
CACHE_CELLS = 250_000


def audit():
    families = []
    for count in (1, 2, 4, 8, 16, 32, 64):
        clauses = tuple(clause for i in range(count)
                        for clause in ((2*i+1, 2*i+2), (-2*i-1, 2*i+2)))
        modes = {}
        for cache in (False, True):
            solver = ComponentSolver(cache=cache, max_cache_cells=CACHE_CELLS)
            run = solver.solve(clauses, max_work=None)
            assert run['status'] == 'YES'
            assert all(run['model'][2*i+2] for i in range(count))
            if cache:
                assert run['metrics']['completed_states'] == (2 if count == 1 else 3)
                assert run['metrics']['nontrivial_cache_hits'] == count - 1
            modes['shared' if cache else 'uncached'] = run
        families.append({'copies': count, 'variables': 2*count, 'literal_slots': 4*count, 'runs': modes})

    groups = []
    for n, budget in CASES:
        feasible = semantic_catalog(n, budget)
        cases, statuses, totals, comparisons = [], {}, {}, Counter()
        for name in ('uncached', 'shared'):
            statuses[name], totals[name] = Counter(), Counter()
        for table in range(1 << (1 << n)):
            runs = {}
            for name, cache in (('uncached', False), ('shared', True)):
                run = search_shared(n, budget, table, cache=cache,
                                    max_work_per_extract=WORK_CAP, max_cache_cells=CACHE_CELLS)
                expected = 'YES' if table in feasible else 'NO'
                assert run['status'] == 'UNKNOWN' or run['status'] == expected
                if run['witness']:
                    assert witness_table(run['witness']) == table
                for iteration in run['iterations']:
                    if iteration['witness']:
                        value = witness_table(iteration['witness'])
                        assert all(value >> row & 1 == bit
                                   for row, bit in run['examples'][:iteration['sample_count']])
                    assert iteration['cache_cells_after'] <= CACHE_CELLS
                    for key in ('computed_states', 'completed_states', 'cache_hits',
                                'nontrivial_cache_hits', 'cross_query_cache_hits',
                                'cache_capacity_skips', 'component_splits'):
                        totals[name][key] += iteration['metrics'][key]
                run['total_work_units'] = sum(run[key] for key in ('compile_work_units', 'update_work_units',
                                               'verification_work_units', 'extraction_work_units'))
                totals[name]['total_work_units'] += run['total_work_units']
                totals[name]['extraction_work_units'] += run['extraction_work_units']
                totals[name]['max_cache_cells'] = max(totals[name]['max_cache_cells'], run['cache_cells'])
                statuses[name][run['status']] += 1
                runs[name] = run
            if all(r['status'] != 'UNKNOWN' for r in runs.values()):
                delta = runs['shared']['total_work_units'] - runs['uncached']['total_work_units']
                comparisons['both_complete'] += 1
                comparisons['shared_work_' + ('lower' if delta < 0 else 'higher' if delta > 0 else 'equal')] += 1
            else:
                comparisons['has_unknown'] += 1
                if runs['shared']['status'] != 'UNKNOWN':
                    comparisons['only_shared_complete'] += 1
                elif runs['uncached']['status'] != 'UNKNOWN':
                    comparisons['only_uncached_complete'] += 1
            cases.append({'target': table, 'ground_truth_for_audit_only': 'YES' if table in feasible else 'NO',
                          'runs': runs})
        groups.append({'n': n, 'gate_budget': budget, 'truth_tables': len(cases),
                       'feasible_functions': len(feasible),
                       'statuses': {name: dict(v) for name, v in statuses.items()},
                       'totals': {name: dict(v) for name, v in totals.items()},
                       'comparison': dict(comparisons), 'cases': cases})
    return {'schema_version': 1, 'all_checks_passed': True, 'truth_tables': 288, 'searches': 576,
            'max_work_per_extract': WORK_CAP, 'max_cache_cells': CACHE_CELLS,
            'fixed_family': families, 'groups': groups,
            'scope': 'Exact residual sharing with an amortized bound in the number of distinct subproblems; '
                     'that number is not proved polynomial for general MCSP or SAT.',
            'cost_scope': 'Logical event ledger charges restrictions, normalization, cache keys, table storage, '
                          'component discovery, search, model transport, original constraints, updates and '
                          'verification. It is not CPU time or exact bit cost. Only the two new variants share '
                          'this ledger; all UNKNOWN cases remain in the results.',
            'polynomial_general_time_bound': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=Path('results'))
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    result = audit()
    (args.out_dir / 'cnf_component_reuse.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'all_checks_passed': True,
                      'groups': [{k: g[k] for k in ('n', 'gate_budget', 'statuses', 'comparison')}
                                 for g in result['groups']]}, sort_keys=True))


if __name__ == '__main__':
    main()
