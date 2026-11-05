"""Recover shielded parity from raw clauses and test two distinct failure modes."""
import argparse
import hashlib
import json
from pathlib import Path

from pnp_lab.feedback_fixture import LAYERS, feedback_case, shield_clauses
from pnp_lab.feedback_witness import check_feedback_witness, feedback_witness
from pnp_lab.integer_feedback import (check_integer_feedback, integer_feedback_refute,
                                      learn_anchor_clauses)
from pnp_lab.integer_hull import integer_hull_refute
from pnp_lab.modular_barrier import check_preorder, line_fixture
from pnp_lab.modular_padding import peel
from pnp_lab.ternary_flow import scramble


def rowset(cs):
    return {frozenset(c) for c in cs}


def digest(rows):
    return hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest()


def run():
    families, sockets, blind = [], [], []
    proof_sample = word_sample = None
    for v in (4, 12):
        for bad in (False, True):
            seed = 17000 + v
            n, rows, planted, core = feedback_case(v, bad)
            raw, w = scramble(n, rows, planted, seed)
            # This oracle uses the same permutation of all n coordinates; it
            # is not visible to any learner, refuter, or model constructor.
            expected, _ = scramble(n, core, None, seed)
            raw_int = integer_hull_refute(n, raw)
            assert raw_int['status'] == 'UNKNOWN' and raw_int['stats']['scope_complete']
            assert not raw_int['stats']['budget_limited'] and raw_int['stats']['local_rows'] == 0
            assert not peel(n, raw)[1]
            learned = learn_anchor_clauses(n, raw)
            assert learned['complete'] and rowset(learned['clauses']) == rowset(expected)
            q = integer_feedback_refute(n, raw)
            model = feedback_witness(n, raw)
            a = q['stats']
            assert a['anchors'] == 3*v//2 and a['retained_raw'] == 0
            assert a['learned_clauses'] == a['bfs_runs'] == len(core) == 4*v
            assert a['path_steps'] == len(core)*(LAYERS+1) and a['edges_visited'] == 4*LAYERS*len(core)
            case = dict(graph_vertices=v, layers=LAYERS, odd_charge=bad, variables=n,
                        clauses=len(raw), seed=seed, raw_sha256=digest(raw), raw_integer=raw_int['stats'],
                        raw_integer_status=raw_int['status'], private_peel_steps=0, core_recovered_exactly=True,
                        refuter_status=q['status'], refuter=a, constructor_status=model['status'],
                        constructor=model['stats'])
            if bad:
                assert q['status'] == 'UNSAT' and a['backend'] == 'parity_sum'
                assert check_integer_feedback(n, raw, q['certificate'])
                assert model['status'] == 'UNKNOWN' and model['witness'] is None
                terms = q['certificate']['integer']['terms']
                assert len(terms) == v and all(t['weight'] == 1 and t['coeff'] == [1,1,1] for t in terms)
                case.update(combined_status='UNSAT', modulus=2, coefficient_bits=1, terms=len(terms))
                if v == 4:
                    proof_sample = dict(graph_vertices=v, layers=LAYERS, odd_charge=True, seed=seed,
                                        raw_sha256=digest(raw), certificate=q['certificate'])
            else:
                assert q['status'] == 'UNKNOWN' and model['status'] == 'SAT'
                assert check_feedback_witness(n, raw, model['witness']) and check_feedback_witness(n, raw, w)
                case.update(combined_status='SAT', raw_word_checked=True, planted_control_checked=True,
                            distinct_from_planted=(w != model['witness']))
                if v == 4:
                    word_sample = dict(graph_vertices=v, layers=LAYERS, odd_charge=False, seed=seed,
                                       raw_sha256=digest(raw), witness=model['witness'])
            families.append(case)
    # Independent opacity control: every literal has an implication strip.
    for bad in (False, True):
        n, rows, w, _ = feedback_case(4, bad, all_sockets=True)
        raw, w = scramble(n, rows, w, 17170)
        q = integer_feedback_refute(n, raw)
        sat = feedback_witness(n, raw)
        assert q['status'] == sat['status'] == 'UNKNOWN'
        assert not q['stats']['budget_limited'] and not sat['stats']['budget_limited']
        assert q['stats']['anchors'] == q['stats']['learned_clauses'] == 0
        initial = integer_hull_refute(n, raw)
        assert initial['stats']['scope_complete'] and initial['stats']['local_rows'] == 0
        assert not peel(n, raw)[1]
        if not bad:
            assert check_feedback_witness(n, raw, w)
        sockets.append(dict(graph_vertices=4, odd_charge=bad, variables=n, clauses=len(raw),
                            seed=17170, layers=LAYERS, raw_sha256=digest(raw), anchors=0,
                            retained=0, learned=0, status='UNKNOWN', private_peel_steps=0,
                            raw_integer_scopes=initial['stats']['scopes_profiled'], raw_integer_rows=0,
                            checked_sat_control=not bad, reason=sat['reason']))
    # Perfect clause recovery need not reveal an integer equation either.
    k, base = line_fixture(0)
    base = base[:152]
    old = json.loads((Path(__file__).resolve().parents[1]/'results/modular_barrier.json').read_text())
    assert check_preorder(k, base, old['fixture']['tree_preorder'])
    for bad in (True, False):
        f = base if bad else tuple(tuple(map(abs, c)) for c in base)
        rotations = [c[j:]+c[:j] for c in f for j in range(3)]
        n, rows, w = shield_clauses(k, rotations, layers=2, word=None if bad else (1<<k)-1)
        raw, w = scramble(n, rows, w, 17171)
        expected, _ = scramble(n, f, None, 17171)
        p = learn_anchor_clauses(n, raw)
        assert p['complete'] and rowset(p['clauses']) == rowset(expected)
        q = integer_feedback_refute(n, raw)
        sat = feedback_witness(n, raw)
        assert q['status'] == sat['status'] == 'UNKNOWN'
        assert not q['stats']['budget_limited'] and not sat['stats']['budget_limited']
        assert q['stats']['integer']['scope_complete'] and q['stats']['integer']['local_rows'] == 0
        if not bad:
            assert check_feedback_witness(n, raw, w)
        blind.append(dict(variables=n, clauses=len(raw), layers=2, seed=17171, raw_sha256=digest(raw),
                          unsatisfiable=bad, core_clauses=len(f), recovered_exactly=True, status='UNKNOWN',
                          refuter=q['stats'], constructor_reason=sat['reason'], checked_sat_control=not bad))
    return dict(schema_version=1, all_checks_passed=True, parity_families=families,
                anchorless_controls=sockets, integer_blind_controls=blind,
                proof_sample=proof_sample, witness_sample=word_sample,
                summary=dict(parity_inputs=len(families), raw_checked_sat=2, raw_checked_unsat=2,
                             clique_and_prism_vertices=[4,12], max_positive_family_variables=1602,
                             max_positive_family_clauses=3120, max_recovered_clauses=48,
                             largest_parity_proof_terms=12, largest_source_path_steps=816,
                             largest_path_edges_visited=3072, anchorless_controls=len(sockets),
                             recovery_without_decision_controls=len(blind)),
                scope='Finite signed-scrambled controls; no empirical expansion or general SAT complexity claim. The SCC witnesses and path/integer contradictions are checked against original clauses. The two infinite-family arguments and their limits are documented separately.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    r = run()
    (out/'integer_feedback.json').write_text(json.dumps(r, sort_keys=True, indent=2)+'\n')
    print(r['summary'])
