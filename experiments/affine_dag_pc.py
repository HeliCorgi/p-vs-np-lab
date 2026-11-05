"""Replay the direct affine-DAG simulation with explicit Boolean corrections."""
import argparse
from hashlib import sha256
from itertools import combinations_with_replacement, product
import json
from pathlib import Path

from pnp_lab.affine_dag_pc import (DAG_KIND, boolean_zero_pc, clause_indicator,
    masked_affine_dag_pc, poly_mul, raw_affine_clause, replay_affine_dag, squarefree)
from pnp_lab.parity_pc import ONE, _degree, replay_parity_pc


def rank_cut_fixture():
    """The same high-rank clause feeds both a one-high and a two-high rule."""
    raw = [(1,), (-1,), (-2,), (-3,)]
    nodes = [dict(op='input', input=i, clause=raw_affine_clause(c))
             for i, c in enumerate(raw)]
    nodes.extend([
        dict(op='infer', parents=[2, 3], clause=[((2, 3), 1)]),
        dict(op='infer', parents=[0], clause=[((1,), 0), ((2, 3), 0)]),
        dict(op='infer', parents=[1], clause=[((1,), 1), ((2, 3), 0)]),
        dict(op='infer', parents=[5, 6], clause=[((2, 3), 0)]),
        dict(op='infer', parents=[5, 4], clause=[((1,), 0)]),
        dict(op='infer', parents=[0], clause=[((1,), 0), ((1,), 1)]),
        dict(op='infer', parents=[8, 1], clause=[]),
    ])
    return raw, dict(kind=DAG_KIND, variables=4, nodes=nodes)


def run():
    raw, dag = rank_cut_fixture()
    source = replay_affine_dag(4, raw, dag)
    masks = [('linear_parity', frozenset({(2,), (3,)})),
             ('quadratic_with_square', poly_mul(frozenset({(2,), (3,)}),
                                               frozenset({(2,), (4,)})))]
    cases, sample = [], None
    for name, mask in masks:
        result = masked_affine_dag_pc(4, raw, dag, mask, 1)
        proof = result['certificate']
        replay = replay_parity_pc(4, raw, proof)
        assert replay['root'] == mask
        assert not any(node['op'] == 'assumption' for node in proof['nodes'])
        encoded = json.dumps(proof, sort_keys=True, separators=(',', ':')).encode()
        cases.append(dict(name=name, mask=sorted(mask), profile=result['profile'],
                          proof_sha256=sha256(encoded).hexdigest(), proof_bytes=len(encoded),
                          repeated_power_lines=sum(any(len(set(m)) < len(m) for m in p)
                                                   for p in replay['polynomials'])))
        sample = proof
    # Complete basis of the Boolean-vanishing subspace through degree 4 in 3 vars.
    # Each repeated monomial m supplies m + multilinear(m); there are 35-8=27.
    reductions, degree_checks = 0, []
    for d in range(5):
        for monomial in combinations_with_replacement(range(1, 4), d):
            reduced = tuple(sorted(set(monomial)))
            if monomial == reduced:
                continue
            value = frozenset({monomial, reduced})
            proof = boolean_zero_pc(3, value)
            assert replay_parity_pc(3, [], proof)['root'] == value
            assert proof['degree'] <= d
            reductions += 1
            degree_checks.append(proof['degree'])
    assert reductions == 27
    # Enumerate every affine flat of F2^3 and test the rank-degree indicators.
    literals = [(tuple(i+1 for i in range(3) if mask >> i & 1), bit)
                for mask in range(1, 8) for bit in (0, 1)]
    from itertools import combinations
    flats = {}
    assignments = list(product((0, 1), repeat=3))
    for width in range(4):
        for clause in combinations(literals, width):
            info = clause_indicator(3, clause)
            actual = []
            for a in assignments:
                false = all((sum(a[v-1] for v in scope)+constant) % 2 == 0
                            for scope, constant in clause)
                observed = sum(all(a[v-1] for v in monomial)
                               for monomial in info['polynomial']) % 2
                assert observed == false
                actual.append(int(false))
            flats[tuple(actual)] = info['rank']
            if info['rank'] is not None:
                assert sum(actual) == 2**(3-info['rank'])
                assert _degree(info['polynomial']) == info['rank']
            else:
                assert not any(actual)
    assert len(flats) == 52
    cases_total = {name: sum(c['profile']['cases'][name] for c in cases)
                   for name in cases[0]['profile']['cases']}
    return dict(schema_version=1, all_checks_passed=True, raw_clauses=raw,
                affine_dag=dag, cases=cases, sample_ordinary_pc_certificate=sample,
                summary=dict(masked_dag_conversions=len(cases),
                             ordinary_pc_nodes=sum(c['profile']['proof_nodes'] for c in cases),
                             maximum_ordinary_degree=max(c['profile']['proof_degree'] for c in cases),
                             source_shared_nodes=source['profile']['shared_nodes'],
                             rule_cases=cases_total, boolean_ideal_basis_proofs=reductions,
                             all_three_variable_affine_flats_checked=len(flats),
                             no_unchecked_path_axioms=True),
                scope='Finite semantic DAGs and explicit ordinary-PC traces only. The roots are the supplied masks, not necessarily 1. No minimum-degree or asymptotic lower bound is inferred from these tiny UNSAT controls; those require the separate dimension and expander proofs.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out / 'affine_dag_pc.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(report['summary'])
