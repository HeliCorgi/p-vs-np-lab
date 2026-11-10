#!/usr/bin/env python3
"""Finite controls for the formal degree-accounted extension transfer."""
import argparse
from itertools import product
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.circuit_extensions import inner_product
from pnp_lab.extension_degree import (
    degree, evaluate, expand, gate_residuals, ordinary_product, reduction_circuit)


def audit():
    rows = []
    for n in (1, 2, 4, 8, 12):
        for kind in ('AND', 'OR', 'XOR'):
            circuit = reduction_circuit(n, kind, balanced=True)
            result = expand(circuit)
            q = result['coordinates'][circuit.output-1]
            boolean_image = ordinary_product(q, q) ^ q if kind != 'OR' else None
            # The OR control concerns sparse expansion size; its dense ordinary
            # square is not computed. Null below records this unrun operation.
            tested = 0
            if n <= 8:
                residuals = gate_residuals(circuit, result['coordinates'])
                for word in product((False, True), repeat=n):
                    expected = (all(word) if kind == 'AND' else
                                any(word) if kind == 'OR' else sum(word) % 2)
                    if evaluate(q, word) != expected:
                        raise AssertionError('Output semantics mismatch')
                    if any(evaluate(p, word) for p in residuals):
                        raise AssertionError('Definition fails all-cube condition')
                    tested += 1
            expected_degree = 1 if kind == 'XOR' else n
            expected_terms = n if kind == 'XOR' else 1 if kind == 'AND' else 2**n-1
            if result['output_degree'] != expected_degree or len(q) != expected_terms:
                raise AssertionError('Degree/support formula mismatch')
            rows.append(dict(inputs=n, operation=kind, gates=len(circuit.gates),
                             coordinate_degree=result['coordinate_degree'],
                             output_degree=result['output_degree'], output_terms=len(q),
                             multiplication_depth=result['multiplication_depth'],
                             expansion_work=result['work'], truth_assignments_checked=tested,
                             ordinary_boolean_image_degree=(degree(boolean_image)
                                                            if boolean_image is not None else None)))
    ip = expand(inner_product(32))
    if ip['coordinate_degree'] != 2 or ip['output_terms'] != 32:
        raise AssertionError('Inner-product control mismatch')
    return dict(all_checks_passed=True, families=rows,
                inner_product_control=dict(pairs=32, coordinate_degree=ip['coordinate_degree'],
                                           output_terms=ip['output_terms']),
                transfer_theorem='D*B degree budget; formal proof in ExtensionSubstitution.lean',
                size_simulation_claimed=False, unrestricted_extension_lower_bound=False,
                p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), sort_keys=True, indent=2) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'extension_degree.json').write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
