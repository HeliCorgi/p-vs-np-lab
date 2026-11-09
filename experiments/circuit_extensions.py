#!/usr/bin/env python3
"""Bounded audit of nonlinear extensions; not a general SAT algorithm."""
import argparse
from itertools import product
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from pnp_lab.circuit_extensions import inner_product, refute_duplicate, tseitin
from pnp_lab.resolution_closure import check_resolution


def audit():
    projection = []
    for m in (1, 2, 3):
        circuit = inner_product(m)
        n, cs = tseitin(circuit)
        count = 0
        for word in product((False, True), repeat=n):
            accepted = all(any(word[abs(l)-1] == (l > 0) for l in c) for c in cs)
            if accepted:
                if sum(word[i] * word[m+i] for i in range(m)) % 2 != 1:
                    raise AssertionError('Spurious projected witness')
                count += 1
        expected = (2**m-1)*2**(m-1)
        if count != expected:
            raise AssertionError('Unique-extension count mismatch')
        projection.append(dict(m=m, variables=n, clauses=len(cs), witnesses=count,
                               assignments_checked=2**n))
    refutations = []
    for m in (1, 2, 3, 8, 64, 1024):
        result = refute_duplicate(inner_product(m))
        checked = check_resolution(result['variables'], result['clauses'], result['certificate'])
        if not checked:
            raise AssertionError('Independent replay failed')
        refutations.append(dict(m=m, variables=result['variables'], clauses=len(result['clauses']),
                                certificate_verified=checked, **result['stats']))
    return dict(all_checks_passed=True,
                scope='Finite verification of explicit circuit encodings and resolution proofs; '
                      'all-size proof and complexity qualifications are in docs/circuit_extensions.md.',
                projection=projection, duplicate_circuit_refutations=refutations,
                general_sat_solver=False, p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), sort_keys=True, indent=2) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'circuit_extensions.json').write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
