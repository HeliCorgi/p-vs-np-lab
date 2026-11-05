"""Ordinary-PC trace replay for parity discharge and weighted branch gluing."""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from pnp_lab.parity_pc import check_parity_pc, parity_tree_to_pc, replay_parity_pc
from pnp_lab.parity_query import KIND, check_parity_query, parity_query_refute


def _audit(n, raw, tree, name):
    assert check_parity_query(n, raw, tree)
    result = parity_tree_to_pc(n, raw, tree)
    assert result['status'] == 'UNSAT'
    proof = result['certificate']
    assert check_parity_pc(n, raw, proof)
    replay = replay_parity_pc(n, raw, proof)
    repeated = sum(any(len(set(m)) < len(m) for m in p) for p in replay['polynomials'])
    # Deliberately compute what an *unjustified implicit reduction* would hide.
    # This comparison is never used by the ordinary-PC checker.
    reduced_degree = 0
    for polynomial in replay['polynomials']:
        counts = Counter(tuple(sorted(set(m))) for m in polynomial)
        reduced_degree = max(reduced_degree, max((len(m) for m, count in counts.items()
                                                 if count % 2), default=0))
    assert repeated and reduced_degree < proof['degree']
    assert not check_parity_pc(n, raw, dict(proof, degree=reduced_degree))
    assert not any(node['op'] == 'assumption' for node in proof['nodes'])
    stats = result['stats']
    assert (1 << stats['certified_rank']) <= stats['weighted_leaf_mass']
    encoded = json.dumps(proof, sort_keys=True, separators=(',', ':')).encode()
    return dict(name=name, variables=n, raw_clauses=raw, parity_tree=tree,
                stats=stats, proof_sha256=sha256(encoded).hexdigest(), proof_bytes=len(encoded),
                repeated_power_lines=repeated, hypothetical_reduced_degree=reduced_degree,
                false_reduced_degree_claim_rejected=True,
                raw_binding_checked=True, no_path_axioms_at_root=True), proof


def run():
    cases = []
    sample = None
    for n in (2, 3):
        raw = list(product(*[(i, -i) for i in range(1, n+1)]))
        tree = parity_query_refute(n, raw)['certificate']
        case, proof = _audit(n, raw, tree, f'balanced_parity_{n}')
        cases.append(case)
        if sample is None:
            sample = proof
    raw = [(1,), (-1, 2), (-1, -2, 3), (-1, -2, -3)]
    tree = dict(kind=KIND, root=0, nodes=[
        dict(query=[1], zero=1, one=2), dict(clause=0),
        dict(query=[2], zero=3, one=4), dict(clause=1),
        dict(query=[3], zero=5, one=6), dict(clause=2), dict(clause=3)])
    case, _ = _audit(3, raw, tree, 'nonuniform_comb')
    assert case['stats']['actual_leaf_degree_histogram'] == {'1': 1, '2': 1, '3': 2}
    assert case['stats']['certified_rank'] < case['stats']['leaf_count_degree_bound']
    cases.append(case)
    return dict(schema_version=1, all_checks_passed=True, cases=cases,
                sample_first_ordinary_pc_certificate=sample,
                summary=dict(ordinary_pc_refutations=len(cases),
                             explicit_arithmetic_nodes=sum(case['stats']['proof_nodes'] for case in cases),
                             maximum_degree=max(case['stats']['proof_degree'] for case in cases),
                             branch_compositions=sum(len(case['stats']['branch_glue']) for case in cases),
                             repeated_power_lines=sum(case['repeated_power_lines'] for case in cases),
                             underestimated_degrees_rejected=len(cases),
                             nonuniform_leaf_rank_checked=True),
                scope='Exact ordinary F2 polynomial traces, with repeated variables retained and Boolean axioms explicit. Finite checks of the discharge/rank composition, not a search for minimum PC degree or a polynomial-size trace-conversion claim. Full-cube inputs have much shorter direct sum proofs; the conversion overhead is not a lower bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out / 'parity_pc.json').write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(report['summary'])
