"""Independent raw-clause replay of complete-parity-block decision trees.

Small graph controls are not expansion certificates and do not measure a
resolution lower bound.  Their entire Boolean cubes are routed through the
generated trees to test the leaf meaning separately from Gaussian checking.
"""
import argparse
from itertools import combinations, product
import json
from pathlib import Path

from pnp_lab.feedback_fixture import cubic_tseitin
from pnp_lab.modular_hull import modular_hull_refute, check_modular_hull
from pnp_lab.parity_query import check_parity_query, parity_query_refute
from pnp_lab.ternary_flow import divergence, prism_edges, scramble


def word_ok(raw, word):
    return all(any(bool(word >> (abs(lit)-1) & 1) == (lit > 0) for lit in row)
               for row in raw)


def semantic_replay(n, raw, certificate):
    """All assignments, without the checker's Gaussian elimination routines."""
    nodes = certificate['nodes']
    used = set()
    questions = 0
    for word in range(1 << n):
        ix = certificate['root']
        while 'query' in nodes[ix]:
            node = nodes[ix]
            bit = sum((word >> (v-1)) & 1 for v in node['query']) % 2
            ix = node['one' if bit else 'zero']
            questions += 1
        leaf = nodes[ix]
        assert set(leaf) == {'clause'}  # no actual input reaches a vacuous leaf
        used.add(ix)
        assert not any(bool(word >> (abs(lit)-1) & 1) == (lit > 0)
                       for lit in raw[leaf['clause']])
    return dict(assignments=1 << n, questions=questions, reached_leaves=len(used))


def run():
    cases = []
    sample = None
    for vertices in (4, 6):
        edges = tuple(combinations(range(4), 2)) if vertices == 4 else prism_edges(3)
        values = tuple((i+1) % 2 for i in range(len(edges)))
        for bad in (False, True):
            charges = list(divergence(edges, values, vertices, 2))
            if bad:
                charges[0] ^= 1
            n, raw = cubic_tseitin(edges, charges)
            word = None if bad else sum(bit << i for i, bit in enumerate(values))
            seed = 19000 + vertices
            raw, word = scramble(n, raw, word, seed)
            result = parity_query_refute(n, raw)
            case = dict(vertices=vertices, variables=n, clauses=len(raw), seed=seed,
                        truth='UNSAT' if bad else 'SAT', status=result['status'],
                        stats=result['stats'])
            if bad:
                certificate = result['certificate']
                assert result['status'] == 'UNSAT'
                assert check_parity_query(n, raw, certificate)
                case['semantic_replay'] = semantic_replay(n, raw, certificate)
                case['certificate_bytes'] = len(json.dumps(certificate, sort_keys=True,
                                                          separators=(',', ':')).encode())
                baseline = modular_hull_refute(n, raw, prime=2)
                assert baseline['status'] == 'UNSAT'
                assert check_modular_hull(n, raw, baseline['certificate'])
                case['previous_prime_two_affine_sum'] = dict(status='UNSAT', checked=True)
                if sample is None:
                    sample = dict(variables=n, raw_clauses=raw, certificate=certificate)
            else:
                assert result['status'] == 'UNKNOWN' and result['certificate'] is None
                assert word is not None and word_ok(raw, word)
                case['raw_sat_word_hex'] = hex(word)
            cases.append(case)
    # Arbitrary overlap, duplicate support, duplicate literal, and an extra
    # nonlinear clause: the discovery theorem is not restricted to graph stars.
    def parity(scope, rhs):
        return [tuple(-v if bit else v for v, bit in zip(scope, word))
                for word in product((0, 1), repeat=len(scope)) if sum(word) % 2 != rhs]
    raw = parity((1, 2, 3), 0) + parity((2, 3, 4), 1) + parity((1, 4), 0)
    raw += [(1, 3, 4), raw[0], (*raw[0], raw[0][0]), (1, -1, 4)]
    result = parity_query_refute(4, raw)
    assert result['status'] == 'UNSAT' and check_parity_query(4, raw, result['certificate'])
    overlap = dict(variables=4, clauses=len(raw), stats=result['stats'],
                   semantic_replay=semantic_replay(4, raw, result['certificate']))
    all_patterns = parity((1, 2), 0) + parity((1, 2), 1)
    result = parity_query_refute(2, all_patterns)
    assert result['status'] == 'UNSAT' and result['stats']['selected_blocks'] == 2
    duplicate_support = dict(variables=2, clauses=len(all_patterns), stats=result['stats'],
                            semantic_replay=semantic_replay(2, all_patterns, result['certificate']))
    unsat = [case for case in cases if case['truth'] == 'UNSAT']
    return dict(schema_version=1, all_checks_passed=True, graph_cases=cases,
                overlap_control=overlap, opposite_blocks_same_support=duplicate_support,
                sample_raw_certificate=sample,
                summary=dict(graph_inputs=len(cases), raw_checked_refutations=4,
                             graph_sat_siblings_checked=2,
                             previous_affine_sum_refutations=len(unsat),
                             all_assignment_replays=sum(case['semantic_replay']['assignments'] for case in unsat)
                                                   + overlap['semantic_replay']['assignments']
                                                   + duplicate_support['semantic_replay']['assignments'],
                             largest_query_support=max(case['stats']['max_query_support'] for case in unsat),
                             largest_tree_nodes=max(case['stats']['nodes'] for case in unsat)),
                scope='Independent exact raw-clause path checking and all-word routing on small controls. The raw finder uses no graph metadata. These controls were already easy for the previous F2 affine-sum refuter; no new separation from affine-terminal trees or measured asymptotic lower bound is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out / 'parity_query.json').write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
    print(report['summary'])
