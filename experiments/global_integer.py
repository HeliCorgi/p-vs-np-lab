"""A modulus born only after composing locally saturated integer relations."""
import argparse
import hashlib
import json
from pathlib import Path

from pnp_lab.global_lattice_fixtures import carry_cycle, carry_field_values
from pnp_lab.integer_hull import integer_hull_refute, check_integer_hull
from pnp_lab.integer_probe import integer_probe_refute
from pnp_lab.mixed_modular import mixed_modular_refute, check_field_bridge
from pnp_lab.modular_barrier import line_fixture, check_preorder
from pnp_lab.modular_hull import modular_hull_refute
from pnp_lab.ternary_flow import scramble


def holds(clauses, word):
    return all(any(bool(word >> (abs(l)-1) & 1) == (l > 0) for l in c) for c in clauses)


def radical(m):
    result, d = 1, 2
    while d*d <= m:
        if m % d == 0:
            result *= d
            while m % d == 0:
                m //= d
        d += 1
    return result * (m if m > 1 else 1)


def blind_twins():
    """Replay the saved phase14 tree; do not launch a fresh refutation search."""
    saved = json.loads((Path(__file__).resolve().parents[1]/'results'/'modular_barrier.json').read_text())
    n, rows = line_fixture(saved['fixture']['seed'])
    negative = rows[:saved['fixture']['prefix']]
    proof = saved['fixture']['tree_preorder']
    assert n == 31 and len(negative) == 152
    assert check_preorder(n, negative, proof)
    positive = tuple(tuple(map(abs, c)) for c in negative)
    positive_word = (1 << n)-1
    assert holds(positive, positive_word)
    cases = []
    for label, clauses in (('checked_unsat', negative), ('checked_sat', positive)):
        root = integer_hull_refute(n, clauses)
        assert root['status'] == 'UNKNOWN'
        assert root['stats']['scope_complete'] and root['stats']['local_rows'] == 0
        assert root['stats']['integer_feasible'] is True
        assert not root['stats']['budget_limited']
        probe = integer_probe_refute(n, clauses, max_calls=None, private_peel=False)
        assert probe['status'] == 'UNKNOWN' and probe['reason'] == 'no further forced value found'
        assert probe['stats']['integer_calls'] == 2*n+1
        assert probe['stats']['learned_units'] == 0
        assert not probe['stats']['budget_limited'] and not probe['stats']['inner_budget_limited']
        cases.append(dict(truth=label, variables=n, clauses=len(clauses),
                          root_status=root['status'], root_stats=root['stats'],
                          probe_status=probe['status'], probe_reason=probe['reason'],
                          probe_stats={k: v for k, v in probe['stats'].items() if k != 'calls'},
                          checked_original_boolean_word=(label == 'checked_sat')))
    return dict(cases=cases, source_report='results/modular_barrier.json',
                original_unsat_tree_checked=True, refutation_nodes=saved['summary']['refutation_nodes'],
                tree_preorder_sha256=hashlib.sha256(json.dumps(proof, separators=(',', ':')).encode()).hexdigest(),
                positive_witness_hex=hex(positive_word),
                same_unsigned_supports=True)


def run():
    cases = []
    bridges = []
    sample = None
    for m, bad_total in ((4, 2), (5, 1), (7, 1), (8, 2), (9, 3), (25, 5), (49, 7)):
        for bad in (False, True):
            total = bad_total if bad else (m if m % 2 else 0)
            n, clauses, word, metadata = carry_cycle(m, total, wire_length=10)
            seed = 15100 + m
            raw, renamed_word = scramble(n, clauses, word, seed)
            result = integer_hull_refute(n, raw)
            stats = result['stats']
            assert stats['scope_complete'] and not stats['budget_limited']
            assert stats['local_torsion_histogram'] == {'[]': stats['scopes_profiled']}
            assert stats['congruence_rows'] == 0
            assert result['status'] == ('UNSAT' if bad else 'UNKNOWN')
            if bad:
                cert = json.loads(json.dumps(result['certificate']))
                assert check_integer_hull(n, raw, cert)
                assert cert['modulus'] == m and cert['residual_rhs'] != 0
                assert all(t['modulus'] == 0 for t in cert['terms'])
                if sample is None:
                    sample = dict(variables=n, clauses=raw, certificate=cert,
                                  construction=dict(gates=m, total=total, wire_length=10, scramble_seed=seed))
            else:
                assert stats['integer_feasible'] is True
                assert renamed_word is not None and holds(raw, renamed_word)
            independent_fields = []
            for p in (2, 3):
                answer = modular_hull_refute(n, raw, prime=p)
                assert answer['status'] == 'UNKNOWN'
                independent_fields.append(dict(prime=p, status=answer['status'],
                                               local_rows=answer['stats']['local_rows']))
            field_controls = []
            for p in (2, 3, 5, 7, 11):
                values = carry_field_values(n, metadata, p)
                assert (values is not None) == (m % p != 0 or total % p == 0)
                field_controls.append(dict(prime=p, equations_feasible=values is not None))
            if bad and m in (4, 5, 7, 9):
                bridge = mixed_modular_refute(n, raw, bridge_width=3,
                                             max_probes=100000, max_short_rows=50000)
                assert bridge['status'] == 'UNSAT'
                assert check_field_bridge(n, raw, bridge['certificate'])
                bridges.append(dict(gates=m, total=total, status=bridge['status'],
                                    stats=bridge['stats']))
            cases.append(dict(gates=m, total=total, wire_length=10, scramble_seed=seed,
                              variables=n, clauses=len(raw), unsatisfiable=bad,
                              status=result['status'], reason=result['reason'], stats=stats,
                              checked_original_boolean_word=renamed_word is not None,
                              all_prime_linear_systems_feasible_by_criterion=(total % radical(m) == 0),
                              tested_field_equations=field_controls,
                              independent_field_hulls=independent_fields))
    largest = cases[-1]
    blind = blind_twins()
    return dict(schema_version=1, all_checks_passed=True, carry_cycles=cases,
                prior_boolean_bridge_controls=bridges, sample_refutation=sample,
                local_information_blind_twins=blind,
                summary=dict(raw_inputs=len(cases)+len(blind['cases']), carry_cycle_inputs=len(cases),
                             integer_refutations=sum(c['unsatisfiable'] for c in cases),
                             checked_sat_siblings=sum(c['checked_original_boolean_word'] for c in cases),
                             discovered_moduli=[c['stats']['discovered_modulus'] for c in cases if c['unsatisfiable']],
                             all_prime_consistent_unsat_controls=sum(c['unsatisfiable'] and c['all_prime_linear_systems_feasible_by_criterion'] for c in cases),
                             local_torsion_free_scopes=sum(c['stats']['scopes_profiled'] for c in cases),
                             independent_field_runs=2*len(cases), prior_bridge_refutations=len(bridges),
                             blind_twin_inputs=len(blind['cases']),
                             blind_twin_root_rows=0,
                             blind_twin_probe_calls=sum(c['probe_stats']['integer_calls'] for c in blind['cases']),
                             blind_twin_learned_units=0,
                             largest_variables=largest['variables'], largest_clauses=largest['clauses'],
                             largest_proof_terms=largest['stats']['certificate_terms'],
                             largest_modulus=largest['stats']['discovered_modulus'],
                             max_coefficient_bits=max(c['stats']['max_coefficient_bits'] for c in cases),
                             max_combination_bits=max(c['stats']['max_combination_bits'] for c in cases),
                             max_rhs_bits=max(c['stats']['max_rhs_bits'] for c in cases)),
                scope='Global integer obstructions from torsion-free local tables. Prime-field feasibility concerns field-valued assignments, not a common Boolean model. The prior mixed Boolean bridge also refutes its checked carry-cycle controls. A separately checked UNSAT/SAT pair gives zero root equations and no learned units after every one-bit integer probe, without a budget cap; this is not a complete SAT algorithm or a P versus NP result.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out-dir', type=Path, required=True)
    out = parser.parse_args().out_dir
    out.mkdir(parents=True, exist_ok=True)
    report = run()
    (out/'global_integer.json').write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    print(report['summary'])
