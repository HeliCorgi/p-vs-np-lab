#!/usr/bin/env python3
"""Fixed paired test of retained conflict information; not a P versus NP proof.

This protocol is committed before the solver/panel is executed. The candidate
uses only ordinary resolution, whose known expander-Tseitin lower bounds already
rule out a polynomial total-cost general decider of this form. The finite audit
tests rescue of the physical examples and costs of retention, not that theorem.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
sys.path.insert(0, str(ROOT))
from experiments.physical_restart_bridge import block_cnf
from pnp_lab.physical_sat import restart_sample
from pnp_lab.resolution_closure import check_resolution
from pnp_lab.retained_learning import replay_trace, solve
from pnp_lab.sat_scaling import (check_row_contradiction, gaussian, graph_xor_cnf,
                                 random_three_cnf, recognize_xor, satisfies)

PROTOCOL = dict(
    version=1,
    physical_blocks=[1, 4, 16],
    graph_xor_variables=[12, 24, 36, 48],
    random_variables=[12, 24, 36, 48],
    seeds=[0, 1],
    pigeonhole_holes=[2, 3, 4, 5],
    max_work=200_000,
    max_proof_literals=50_000,
    max_proof_nodes=10_000,
    max_learned_literals=10_000,
    max_depth=128,
    decision_rule='lowest index in an unsatisfied clause, false first',
    backtracking='conflict-directed in both modes',
    unknown_policy='retain all unfinished outcomes, no cap increases',
)


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def signed_rename(n, clauses, seed):
    rng = random.Random(seed)
    labels = list(range(1, n+1))
    rng.shuffle(labels)
    labels = [v if rng.getrandbits(1) else -v for v in labels]
    changed = [tuple(labels[abs(lit)-1] if lit > 0 else -labels[abs(lit)-1] for lit in c)
               for c in clauses]
    rng.shuffle(changed)
    return tuple(changed)


def split_cnf(n, clauses):
    """Standard existential width-three chain; no solving or learned advice."""
    result = []
    for clause in clauses:
        rest = tuple(clause)
        while len(rest) > 3:
            n += 1
            result.append((rest[0], rest[1], n))
            rest = (-n,)+rest[2:]
        result.append(rest)
    return n, tuple(result)


def pigeonhole(holes):
    if type(holes) is not int or holes < 1:
        raise ValueError('positive hole count required')
    pigeons = holes+1
    var = lambda pigeon, hole: pigeon*holes+hole+1
    clauses = [tuple(var(p, h) for h in range(holes)) for p in range(pigeons)]
    for h in range(holes):
        clauses.extend((-var(p, h), -var(q, h)) for p, q in combinations(range(pigeons), 2))
    return split_cnf(pigeons*holes, clauses)


def panel():
    for blocks in PROTOCOL['physical_blocks']:
        n, original = block_cnf(blocks, connected=True)
        for seed in PROTOCOL['seeds']:
            yield dict(family='connected_physical', size=blocks, n=n, seed=seed,
                       clauses=signed_rename(n, original, seed), expected='SAT')
    for n in PROTOCOL['graph_xor_variables']:
        for seed in PROTOCOL['seeds']:
            yield dict(family='graph_xor_odd', size=n, n=n, seed=seed,
                       clauses=graph_xor_cnf(n, True, seed), expected='UNSAT')
    for n in PROTOCOL['random_variables']:
        for seed in PROTOCOL['seeds']:
            yield dict(family='random_3sat_6', size=n, n=n, seed=seed,
                       clauses=random_three_cnf(n, 6, 1, seed), expected=None)
    for holes in PROTOCOL['pigeonhole_holes']:
        n, clauses = pigeonhole(holes)
        yield dict(family='pigeonhole_3cnf', size=holes, n=n, seed=None,
                   clauses=clauses, expected='UNSAT')


def check_answer(n, clauses, answer):
    masks = replay_trace(n, clauses, answer['trace'])
    if answer['status'] == 'SAT':
        if answer['witness'] is None or not satisfies(clauses, answer['witness']):
            raise AssertionError('invalid SAT witness')
    elif answer['status'] == 'UNSAT':
        if not check_resolution(n, clauses, answer['certificate']):
            raise AssertionError('invalid ordinary-resolution refutation')
    elif answer['status'] != 'UNKNOWN':
        raise AssertionError('invalid solver status')
    if answer['status'] != 'SAT' and answer['witness'] is not None:
        raise AssertionError('non-SAT answer supplied a witness')
    if answer['status'] != 'UNSAT' and answer['certificate'] is not None:
        raise AssertionError('non-UNSAT answer supplied a refutation')
    count = slots = 0
    seen = set()
    for event in answer['learned']:
        index = event['node']
        if type(index) is not int or not 0 <= index < len(masks) or index in seen:
            raise AssertionError('bad or duplicate learned consequence')
        seen.add(index)
        count += 1
        slots += sum(x.bit_count() for x in masks[index])
        if event['clauses'] != count or event['literal_slots'] != slots:
            raise AssertionError('learned-memory trace is inconsistent')
    if (count != answer['stats']['learned_clauses'] or slots != answer['stats']['learned_literal_slots']):
        raise AssertionError('learned-memory totals are inconsistent')
    return dict(all_trace_nodes_replayed=len(masks), learned_nodes_replayed=count,
                witness_checked=answer['status'] == 'SAT',
                refutation_checked=answer['status'] == 'UNSAT')


def audit():
    limits = {key: value for key, value in PROTOCOL.items() if key.startswith('max_')}
    cases = []
    for case in panel():
        n, clauses = case['n'], case['clauses']
        answers = []
        for retain in (False, True):
            answer = solve(n, clauses, retain=retain, **limits)
            checks = check_answer(n, clauses, answer)
            if (case['expected'] and answer['status'] != 'UNKNOWN'
                    and answer['status'] != case['expected']):
                raise AssertionError('contradiction with an independent structured control')
            # Store actual trace hashes, replay results, counters and progress;
            # the deterministic generator recreates full proofs and checks them.
            answers.append(dict(retain=retain, status=answer['status'], reason=answer['reason'],
                                witness=answer['witness'], stats=answer['stats'], checks=checks,
                                trace_sha256=digest(answer['trace']),
                                certificate_sha256=digest(answer['certificate']) if answer['certificate'] else None,
                                learned=answer['learned']))
        completed = {a['status'] for a in answers if a['status'] != 'UNKNOWN'}
        if len(completed) > 1:
            raise AssertionError('paired solvers disagree')
        record = {key: value for key, value in case.items() if key != 'clauses'}
        record.update(clauses=len(clauses), literal_slots=sum(map(len, clauses)),
                      cnf_sha256=digest(clauses), results=answers)
        if case['family'] == 'connected_physical':
            for answer in answers:
                if answer['status'] == 'SAT' and (answer['stats']['decisions'] != case['size']
                        or answer['stats']['conflicts'] > case['size']):
                    raise AssertionError('physical block decision/conflict bound failed')
            baseline = restart_sample(n, clauses, seed=case['seed'], max_attempts=8, ticks_per_attempt=1000)
            if baseline['status'] == 'SAT' and not satisfies(clauses, baseline['witness']):
                raise AssertionError('physical baseline witness failed')
            record['physical_baseline'] = dict(status=baseline['status'], ticks=baseline['ticks'],
                                               literal_inspections=baseline['literal_inspections'],
                                               random_bits=baseline['random_bits'])
        elif case['family'] == 'graph_xor_odd':
            equations = recognize_xor(n, clauses)
            if equations is None:
                raise AssertionError('raw-CNF XOR recognizer failed')
            algebra = gaussian(n, equations)
            if algebra['status'] != 'UNSAT' or not check_row_contradiction(equations, algebra['contradiction']):
                raise AssertionError('independent parity contradiction failed')
            record['algebraic_control'] = dict(status='UNSAT', row_xors=algebra['row_xors'],
                                               rank=algebra['rank'], contradiction_checked=True)
        cases.append(record)

    tally = {str(retain): dict(Counter(r['status'] for case in cases for r in case['results']
                                     if r['retain'] == retain)) for retain in (False, True)}
    comparable = [case for case in cases if all(a['status'] != 'UNKNOWN' for a in case['results'])]
    lower = sum(c['results'][1]['stats']['work'] < c['results'][0]['stats']['work'] for c in comparable)
    equal = sum(c['results'][1]['stats']['work'] == c['results'][0]['stats']['work'] for c in comparable)
    physical_rescued = all(case['results'][1]['status'] == 'SAT'
                          for case in cases if case['family'] == 'connected_physical')
    return dict(all_checks_passed=True, protocol=PROTOCOL, protocol_sha256=digest(PROTOCOL),
                cases=cases, status_counts=tally, physical_panel_rescued=physical_rescued,
                completed_pair_comparison=dict(pairs=len(comparable), lower_work_with_retention=lower,
                                                equal_work=equal, higher_work_with_retention=len(comparable)-lower-equal,
                                                scope='Descriptive only; all censored pairs remain in cases and status_counts.'),
                decision=('Physical panel repaired in both modes; retention is not its necessary cause. Stop the ordinary-resolution mechanism as a general polynomial SAT route.'
                          if physical_rescued else 'Physical repair gate failed; stop without raising the caps.'),
                physical_all_size_scope='The uncapped algorithm solves b connected equality blocks using b decisions and at most b conflicts, in either mode and under signed renamings; proof in src/pnp_lab/retained_learning.py. Fixed experiment caps remain finite.',
                evidence_scope='Independent witness/refutation checks and replay of every proof-prefix node, including UNKNOWN; no asymptotic growth inferred from this panel.',
                known_barrier='Ordinary-resolution expander-Tseitin size lower bounds already exclude polynomial total proof construction for all inputs; see existing docs/robust_ceiling.md. These sampled graphs are not certified asymptotic expanders.',
                remaining_core='A stronger efficiently discoverable representation/inference mechanism with a proved global cost bound; merely keeping more clauses does not supply it.',
                polynomial_general_sat_algorithm=False, p_vs_np_resolved=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path, default=ROOT / 'results')
    args = parser.parse_args()
    report = audit()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir/'retained_learning.json').write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps({key: report[key] for key in ('all_checks_passed', 'physical_panel_rescued', 'status_counts', 'completed_pair_comparison')}))


if __name__ == '__main__':
    main()
