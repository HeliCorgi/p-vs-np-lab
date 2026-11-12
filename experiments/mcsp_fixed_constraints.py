#!/usr/bin/env python3
"""Audit a fixed candidate formula, monotone evidence, and explicit extraction."""

import argparse
from collections import Counter
from itertools import combinations_with_replacement
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT))

from experiments.mcsp_counterexample_search import CASES, semantic_catalog
from pnp_lab.mcsp_counterexample import witness_table
from pnp_lab.mcsp_fixed_constraints import FixedCircuitSpace, search_fixed


EXTRACTION_CAP = 500_000
FOLLOWUP_CAP = 5_000_000


def literal_programs(n, slots):
    """Enumerate literal topological gate lists, without a synthesis oracle."""
    if not slots:
        yield []
        return
    for prefix in literal_programs(n, slots - 1):
        wires = range(n + 2 + len(prefix))
        for a in wires:
            yield prefix + [['NOT', [a]]]
        for a, b in combinations_with_replacement(wires, 2):
            for op in ('AND', 'OR'):
                yield prefix + [[op, [a, b]]]


def reference_model(space, witness):
    """Build all encoding bits by scalar evaluation, outside the SAT engine."""
    values = [-1] * (space.variables + 1)
    gates = witness['gates'] + [['NOT', [0]]] * (space.budget - len(witness['gates']))
    for (ops, left, right), (op, args) in zip(space.gates, gates):
        values[ops[('NOT', 'AND', 'OR').index(op)]] = 1
        ordered = args if op == 'NOT' else sorted(args)
        values[left[ordered[0]]] = 1
        values[right[0 if op == 'NOT' else ordered[1]]] = 1
    values[space.output_choices[witness['output']]] = 1
    for row in range(space.rows):
        wires = [False, True] + [bool(row >> (space.n - 1 - i) & 1) for i in range(space.n)]
        for (a_var, b_var, z_var), (op, args) in zip(space.row_aux[row], gates):
            ordered = args if op == 'NOT' else sorted(args)
            a, b = wires[ordered[0]], False if op == 'NOT' else wires[ordered[1]]
            z = not a if op == 'NOT' else a and b if op == 'AND' else a or b
            for variable, bit in ((a_var, a), (b_var, b), (z_var, z)):
                values[variable] = 1 if bit else -1
            wires.append(z)
        values[space.outputs[row]] = 1 if wires[witness['output']] else -1
    return values


def satisfies_encoding(space, values):
    return all(any(values[abs(lit)] == (1 if lit > 0 else -1) for lit in clause)
               for clause in space.clauses)


def audit_encoding():
    checked, rejected_outputs = 0, 0
    for n, budget in ((1, 0), (1, 1), (2, 1), (2, 2)):
        space = FixedCircuitSpace(n, budget)
        for gates in literal_programs(n, budget):
            for output in range(n + 2 + budget):
                witness = {'n': n, 'gates': gates, 'output': output}
                model = reference_model(space, witness)
                assert satisfies_encoding(space, model)
                table = witness_table(witness)
                assert table == sum(int(model[v] == 1) << row for row, v in enumerate(space.outputs))
                checked += 1
                for variable in space.outputs:
                    model[variable] *= -1
                    assert not satisfies_encoding(space, model)
                    model[variable] *= -1
                    rejected_outputs += 1
    return {'literal_circuit_models_checked': checked, 'wrong_output_models_rejected': rejected_outputs}


def audit():
    encoding = audit_encoding()
    groups = []
    for n, budget in CASES:
        feasible = semantic_catalog(n, budget)
        statuses, totals, cases, followups = Counter(), Counter(), [], []
        shape = None
        for table in range(1 << (1 << n)):
            result = search_fixed(n, budget, table, max_work_per_extract=EXTRACTION_CAP)
            actual = 'YES' if table in feasible else 'NO'
            assert result['status'] == 'UNKNOWN' or result['status'] == actual
            if result['witness']:
                assert witness_table(result['witness']) == table
            for iteration in result['iterations']:
                if iteration['witness']:
                    candidate = witness_table(iteration['witness'])
                    assert all(candidate >> row & 1 == bit
                               for row, bit in result['examples'][:iteration['sample_count']])
                assert iteration['peak_decision_frames'] <= 3 * budget + 1
                assert iteration['peak_trail_slots'] <= result['shape'][0]
            assert result['update'].get('assigned_variables', 0) <= result['shape'][0]
            assert result['shape_unchanged']
            if shape is None:
                shape = result['shape']
            assert result['shape'] == shape
            statuses[result['status']] += 1
            totals.update({'compile_work_units': result['compile']['work_units'],
                           'update_work_units': result['update']['work_units'],
                           'extraction_work_units': result['extraction_work_units'],
                           'accounted_work_units': result['accounted_work_units'],
                           'extraction_calls': len(result['iterations']),
                           'examples': len(result['examples'])})
            cases.append({'target': table, 'ground_truth_for_audit_only': actual, 'run': result})
            if result['status'] == 'UNKNOWN':
                # Disclosed follow-up to EVERY capped case, restarting the same
                # algorithm. Preserve the original cap/status and charge both runs.
                retry = search_fixed(n, budget, table, max_work_per_extract=FOLLOWUP_CAP)
                assert retry['status'] == 'UNKNOWN' or retry['status'] == actual
                if retry['witness']:
                    assert witness_table(retry['witness']) == table
                for iteration in retry['iterations']:
                    if iteration['witness']:
                        candidate = witness_table(iteration['witness'])
                        assert all(candidate >> row & 1 == bit
                                   for row, bit in retry['examples'][:iteration['sample_count']])
                assert retry['shape'] == shape
                followups.append({'target': table, 'run': retry})
        groups.append({'n': n, 'gate_budget': budget, 'truth_tables': len(cases),
                       'feasible_functions': len(feasible), 'fixed_shape': shape,
                       'status_counts': dict(statuses), 'totals': dict(totals), 'cases': cases,
                       'followups': followups,
                       'accounted_work_including_followups': totals['accounted_work_units']
                       + sum(case['run']['accounted_work_units'] for case in followups)})
    return {'schema_version': 1, 'all_checks_passed': True, 'truth_tables': 288,
            'case_selection': 'Same complete panel (2,2),(2,4),(3,3); include all capped/UNKNOWN runs.',
            'max_work_per_extract': EXTRACTION_CAP, 'encoding_audit': encoding,
            'followup_cap': FOLLOWUP_CAP,
            'followup_policy': 'Every primary UNKNOWN is retried from scratch with the same algorithm '
                               'at 10 times the cap. Original UNKNOWN results and both costs are retained.',
            'shape_fields': ['variables', 'clauses', 'literal_slots', 'evidence_slots'],
            'guarantees': {'polynomial_formula_size_in_explicit_N_n_s': True,
                           'formula_shape_independent_of_examples': True,
                           'polynomial_total_monotone_unit_updates': True,
                           'polynomial_working_space_for_extraction': True,
                           'general_polynomial_extraction_time': False},
            'cost_scope': 'Logical work units including construction, evidence, all extraction attempts and '
                          'verification; not exact CPU time or bit operations. Bound diagnostics are charged. '
                          'Serialization and independent auditing are outside the search ledger.',
            'scope': 'Fixed symbolic candidate representation and implemented finite extraction; '
                     'no general polynomial MCSP or SAT algorithm or P vs NP conclusion.',
            'groups': groups}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=Path('results'))
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    result = audit()
    (args.out_dir / 'mcsp_fixed_constraints.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'all_checks_passed': True, 'encoding': result['encoding_audit'],
                      'statuses': [g['status_counts'] for g in result['groups']]}, sort_keys=True))


if __name__ == '__main__':
    main()
