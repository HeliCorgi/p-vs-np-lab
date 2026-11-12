#!/usr/bin/env python3
"""Decision-mode controls for a shared-DAG SAT candidate; no timing thresholds."""
import argparse
from itertools import product
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.extension_degree import expand, ZERO
from pnp_lab.shared_dag_sat import SharedDAG, distributivity_miter, solve_circuit, solve_cnf


def audit():
    rows = []
    for k in (2, 4, 6, 8, 10, 12):
        circuit = distributivity_miter(k)
        default = solve_circuit(circuit)
        order = (k + 1, k + 2, *range(1, k + 1), *range(k + 3, 2 * k + 3))
        selector_first = solve_circuit(circuit, order=order)
        single = solve_circuit(distributivity_miter(k, selectors=1))
        polynomial_zero = expand(circuit)['coordinates'][circuit.output - 1] == ZERO
        manager = SharedDAG()
        prefixes = {manager.from_circuit(circuit)}
        for v in range(1, k - 1):
            prefixes = {manager.cofactor(root, v, bit)
                        for root in sorted(prefixes) for bit in (False, True)}
        checked = 0
        if k <= 4:
            for values in product((False, True), repeat=circuit.inputs):
                if circuit.evaluate(values)[circuit.output - 1]:
                    raise AssertionError('Miter is not identically zero')
                checked += 1
        if (any(r['status'] != 'UNSAT' for r in (default, selector_first, single))
                or not polynomial_zero or len(prefixes) != 2 ** (k - 2)
                or prefixes & {0, 1}
                or default['stats']['states_by_variable'][str(k - 1)] != 2 ** (k - 2)
                or selector_first['stats']['expanded_states'] != 2
                or single['stats']['expanded_states'] != 0):
            raise AssertionError('Shared-DAG family/control failed')
        rows.append(dict(k=k, inputs=circuit.inputs, gates=len(circuit.gates),
                         default_order=default, selector_first=selector_first,
                         single_selector=single,
                         nonconstant_residuals_after_k_minus_2=len(prefixes),
                         proved_state_lower_bound=2 ** (k - 2),
                         independent_polynomial_zero=polynomial_zero,
                         truth_assignments_checked=checked))
    sat = solve_cnf([[1, 2], [-1, 2], [-2, 3]])
    limited = solve_circuit(distributivity_miter(12), max_states=100)
    if sat['status'] != 'SAT' or limited['status'] != 'UNKNOWN':
        raise AssertionError('SAT/budget controls failed')
    return dict(all_checks_passed=True, families=rows, sat_control=sat,
                budget_control=limited, algorithm='fixed-order structural DAG cofactoring',
                normalizer='AND/XOR flattening, constants, complements, all-term common factors',
                state_bound_scope='this implementation and a-first order; paper proof, not Lean',
                work_units_are_bit_operations=False,
                polynomial_state_bound_refuted=True, all_variable_orders_lower_bound=False,
                general_sat_polynomial_time=False, p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), sort_keys=True, indent=2) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'shared_dag_sat.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
