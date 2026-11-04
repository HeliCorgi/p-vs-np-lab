"""Independent exact Boolean-table replay of a discovered nonlinear refutation."""
import argparse
import json
from pathlib import Path

from pnp_lab.modular_barrier import line_fixture
from pnp_lab.relation_proof import check_relation_proof, resolution_to_relations
from pnp_lab.resolution_closure import replay_resolution, resolution_refute
from pnp_lab.ternary_flow import scramble


def run():
    n, clauses = line_fixture(0)
    clauses = clauses[:152]
    cases = []
    sample = None
    first_binary = None
    for seed in (None, 16002):
        cs = clauses if seed is None else scramble(n, clauses, None, seed)[0]
        source = resolution_refute(n, cs, width=4)
        assert source['status'] == 'UNSAT'
        result = resolution_to_relations(n, cs, source['certificate'], max_union_width=5)
        assert result['status'] == 'UNSAT'
        assert check_relation_proof(n, cs, result['certificate'])
        positive = tuple(tuple(map(abs, c)) for c in cs)
        assert not check_relation_proof(n, positive, result['certificate'])
        cap = resolution_to_relations(n, cs, source['certificate'], max_union_width=4)
        assert cap['status'] == 'UNKNOWN' and cap['stats']['budget_limited']
        cases.append(dict(scramble_seed=seed, variables=n, clauses=len(cs),
                          search=source['stats'], relations=result['stats'],
                          positive_control_rejects_certificate=True,
                          union_four_cap_returns_unknown=True))
        if seed is None:
            sample = dict(variables=n, clauses=cs, certificate=result['certificate'])
            rows = replay_resolution(n, cs, source['certificate'])
            j = next(i for i, (row, step) in enumerate(zip(rows, source['certificate']['nodes']))
                     if len(row) == 2 and step['op'] == 'resolve')
            table = result['certificate']['nodes'][j]
            first_binary = dict(proof_node=j, clause=sorted(rows[j], key=abs),
                                scope=table['scope'], table=table['table'],
                                allowed_words=[w for w in range(4) if table['table'] >> w & 1],
                                integer_affine_lattice='full Z^2; the missing Boolean pair is lost')
    first = cases[0]['relations']
    assert first['nodes'] == 368 and first['union_width'] == 5
    assert first['enumerated_cells'] == 6398
    assert first_binary['clause'] == [23, -30] and first_binary['table'] == 11
    return dict(schema_version=1, all_checks_passed=True, cases=cases,
                first_retained_binary_relation=first_binary, sample_refutation=sample,
                summary=dict(checked_refutations=len(cases), original_proof_nodes=first['nodes'],
                             original_input_nodes=first['inputs'], original_join_nodes=first['joins'],
                             maximum_stored_relation_scope=first['max_relation_width'],
                             minimum_join_union_width=5,
                             original_enumerated_cells=first['enumerated_cells'],
                             original_stored_table_cells=first['stored_table_cells'],
                             original_proof_bytes=first['certificate_bytes']),
                scope='Exact joins on one shared Boolean assignment followed by existential projection, original coordinates only. Width counts the union before projection. Minimum width five follows from the proper-linear-three-CNF invariant in the accompanying note, not from a capped search. No general polynomial SAT algorithm.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out/'correlation_relations.json').write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    print(report['summary'])
