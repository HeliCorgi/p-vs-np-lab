"""Small proof-carrying conflict search with a paired clause-retention switch.

Unit propagation, first-variable/false-first branching, resolution conflict
analysis, and conflict-directed backtracking are identical in both modes.
Only retain=True feeds proved conflict clauses into subsequent propagation.
There are no restarts, deletion, oracle calls, new variables, or family metadata.
This is a reference implementation, not a competitive or novel CDCL solver.

Each conflict is resolved backwards through its unit reasons until only decision
literals remain. The result is entailed by the original CNF and falsified by
those decisions. If it omits the latest decision, both values of that decision
are refuted and search backtracks past it. Otherwise the two failed branches
resolve on that decision. At depth zero the result is empty. A successful leaf
is checked on the original CNF. With no resource caps the finite decision tree
is complete; there is no polynomial bound on its size or its proof log.

At most 3^n different non-tautological clauses exist. This bounds the number of
distinct retained clauses but is exponential, and merely retaining a valid
consequence does not remove any genuine model of the input. Known resolution
lower bounds apply to this proof mechanism, including shared clauses. Proof
construction and storage are charged separately from propagation. Work units
are a reproducible operation proxy, not CPU seconds or a complete bit-cost model.

ALL-SIZE NARROW REPAIR of physical_restart_bridge's connected four-spin blocks,
also after any signed variable permutation and clause reordering: the abstract
uncapped search needs b decisions and at most b conflicts, with or without
retention. Here 'true block' means the original all-one orientation before the
signed renaming. At every consistent propagation fixed point a touched block
is entirely true: its equality clauses propagate any assigned bit to all four,
and its positive triple rejects an entirely false block. Untouched blocks have
no assignments. A decision in one untouched block either sets it true, or unit
propagation refutes its false value. The latter may also force neighboring
blocks true through connectors, but the only false block is the chosen one.
Its triple conflict and equality reasons involve only that decision, so reverse
resolution derives the single literal requiring its true value, in at most
three resolution steps. Taking the other value succeeds on that block and
never needs to undo an earlier true block. Induct on the remaining blocks.
The retained database adds at most b units and the proof log O(b) constant-width
rows. Even a conservative full-scan implementation uses only polynomial work
on this family (at most O(b) search calls, O(b) propagations per call, O(b) input
clauses per scan). This statement is about the algorithm without the fixed
experiment caps, not a claim that a fixed cap handles every b. It is a logical
repair, not the old nonincreasing one-spin physical trajectory. Retention is
NOT necessary for this family, as the paired runs independently illustrate.
"""
from __future__ import annotations

import json

from .resolution_closure import KIND, _trim
from .sat_scaling import satisfies, validate


class _Budget(Exception):
    pass


def solve(n, clauses, *, retain=True, max_work=200_000,
          max_proof_literals=50_000, max_proof_nodes=10_000,
          max_learned_literals=10_000, max_depth=128):
    clauses = tuple(tuple(c) for c in clauses)
    validate(n, clauses)
    if any(len(c) > 3 for c in clauses):
        raise ValueError('raw input clauses must have width at most three')
    if type(retain) is not bool:
        raise ValueError('retain must be Boolean')
    for value in (max_work, max_proof_literals, max_proof_nodes, max_learned_literals, max_depth):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError('caps must be nonnegative integers or None')
    rows, nodes, known, active, active_set, learned = [], [], {}, [], set(), []
    stats = dict(work=0, literal_inspections=0, resolution_literal_visits=0,
                 proof_record_visits=0, assignment_copy_visits=0, decision_work=0,
                 witness_literal_visits=0, nodes_visited=0, decisions=0,
                 conflicts=0, propagations=0, learned_reason_propagations=0,
                 skipped_sibling_branches=0, attempted_resolutions=0,
                 proof_literal_slots=0, learned_clauses=0, learned_literal_slots=0,
                 maximum_learned_width=0, maximum_depth=0,
                 input_clauses=len(clauses), input_literal_slots=sum(map(len, clauses)))
    input_ids = set()

    def charge(key, amount):
        if max_work is not None and stats['work']+amount > max_work:
            raise _Budget('work_limit')
        stats[key] += amount
        stats['work'] += amount

    def record(row, node):
        charge('proof_record_visits', len(row)+1)
        if row in known:
            return known[row]
        if max_proof_nodes is not None and len(nodes) >= max_proof_nodes:
            raise _Budget('proof_node_limit')
        if max_proof_literals is not None and stats['proof_literal_slots']+len(row) > max_proof_literals:
            raise _Budget('proof_literal_limit')
        index = len(rows)
        rows.append(row)
        nodes.append(node)
        known[row] = index
        stats['proof_literal_slots'] += len(row)
        return index

    def resolve(left, right, pivot):
        a, b = rows[left], rows[right]
        charge('resolution_literal_visits', len(a)+len(b))
        stats['attempted_resolutions'] += 1
        assert pivot in a and -pivot in b
        row = (a-{pivot}) | (b-{-pivot})
        assert not any(-lit in row for lit in row)
        return record(row, dict(op='resolve', left=left, right=right, pivot=pivot))

    def remember(index):
        if retain and index not in active_set:
            row = rows[index]
            if max_learned_literals is not None and stats['learned_literal_slots']+len(row) > max_learned_literals:
                raise _Budget('learned_literal_limit')
            active_set.add(index)
            active.append(index)
            stats['learned_clauses'] += 1
            stats['learned_literal_slots'] += len(row)
            stats['maximum_learned_width'] = max(stats['maximum_learned_width'], len(row))
            learned.append(dict(node=index, work=stats['work'],
                                clauses=stats['learned_clauses'],
                                literal_slots=stats['learned_literal_slots']))
        return index

    def analyze(index, trail):
        for lit, reason in reversed(trail):
            if reason is not None and -lit in rows[index]:
                index = resolve(index, reason, -lit)
        decisions = {lit for lit, reason in trail if reason is None}
        assert all(-lit in decisions for lit in rows[index])
        return remember(index)

    def search(assignment, trail, depth):
        stats['nodes_visited'] += 1
        stats['maximum_depth'] = max(stats['maximum_depth'], depth)
        while True:
            unit, variable = None, None
            for index in active:
                row = rows[index]
                charge('literal_inspections', len(row))
                residual, true = [], False
                for lit in sorted(row, key=lambda x: (abs(x), x)):
                    value = assignment.get(abs(lit))
                    if value is None:
                        residual.append(lit)
                    elif value == (lit > 0):
                        true = True
                if true:
                    continue
                if not residual:
                    stats['conflicts'] += 1
                    return None, analyze(index, trail)
                if len(residual) == 1:
                    unit = residual[0], index
                    break
                smallest = min(map(abs, residual))
                variable = smallest if variable is None else min(variable, smallest)
            if unit is not None:
                lit, reason = unit
                assignment[abs(lit)] = lit > 0
                trail.append(unit)
                stats['propagations'] += 1
                stats['learned_reason_propagations'] += reason not in input_ids
                continue
            if variable is None:
                charge('witness_literal_visits', sum(map(len, clauses)))
                word = sum(1 << (v-1) for v, value in assignment.items() if value)
                assert satisfies(clauses, word)
                return word, None
            break
        if max_depth is not None and depth >= max_depth:
            raise _Budget('decision_depth_limit')
        charge('decision_work', 1)
        stats['decisions'] += 1
        failed = []
        for value in (False, True):
            charge('assignment_copy_visits', len(assignment)+len(trail)+1)
            child = dict(assignment)
            child[variable] = value
            lit = variable if value else -variable
            word, conflict = search(child, trail+[(lit, None)], depth+1)
            if word is not None:
                return word, None
            if -lit not in rows[conflict]:
                stats['skipped_sibling_branches'] += not value
                return None, conflict
            failed.append(conflict)
        # The false branch contains +variable, the true branch -variable.
        return None, remember(resolve(failed[0], failed[1], variable))

    certificate = witness = None
    status, reason = 'UNKNOWN', None
    try:
        for index, clause in enumerate(clauses):
            row_id = record(frozenset(clause), dict(op='input', clause=index))
            input_ids.add(row_id)
            if row_id not in active_set:
                active.append(row_id)
                active_set.add(row_id)
        witness, root = search({}, [], 0)
        if witness is not None:
            status, reason = 'SAT', 'checked_original_witness'
        else:
            assert not rows[root]
            trimmed, target = _trim(nodes, root)
            certificate = dict(kind=KIND, width=max(map(len, rows), default=0),
                               nodes=trimmed, root=target)
            status, reason = 'UNSAT', 'resolution_refutation'
    except _Budget as exc:
        reason = str(exc)
    stats.update(proof_nodes=len(nodes), active_clauses=len(active),
                 proof_width=max(map(len, rows), default=0),
                 proof_trace_bytes=len(json.dumps(nodes, sort_keys=True, separators=(',', ':')).encode()),
                 certificate_bytes=(len(json.dumps(certificate, sort_keys=True,
                                                  separators=(',', ':')).encode()) if certificate else 0))
    return dict(status=status, reason=reason, witness=witness, certificate=certificate,
                trace=nodes, learned=learned, stats=stats, retain=retain)


def replay_trace(n, clauses, trace):
    """Independent mask-based replay, including SAT/UNKNOWN proof prefixes.

    Does not call the solver, its resolution routine, or use its alleged rows.
    Returns positive/negative masks for independently reconstructed consequences.
    """
    validate(n, clauses)
    if not isinstance(trace, list):
        raise ValueError('trace must be a list')
    masks = []
    for i, node in enumerate(trace):
        if not isinstance(node, dict):
            raise ValueError('bad node')
        if node.get('op') == 'input' and set(node) == {'op', 'clause'}:
            j = node['clause']
            if type(j) is not int or not 0 <= j < len(clauses):
                raise ValueError('bad input index')
            positive = negative = 0
            for lit in clauses[j]:
                if lit > 0:
                    positive |= 1 << (lit-1)
                else:
                    negative |= 1 << (-lit-1)
        elif node.get('op') == 'resolve' and set(node) == {'op', 'left', 'right', 'pivot'}:
            a, b, pivot = node['left'], node['right'], node['pivot']
            if (type(a) is not int or type(b) is not int or not 0 <= a < i or not 0 <= b < i
                    or type(pivot) is not int or not 1 <= abs(pivot) <= n):
                raise ValueError('bad parent or pivot')
            pa, na = masks[a]
            pb, nb = masks[b]
            bit = 1 << (abs(pivot)-1)
            if pivot > 0:
                if not pa & bit or not nb & bit:
                    raise ValueError('wrong pivot signs')
                pa ^= bit
                nb ^= bit
            else:
                if not na & bit or not pb & bit:
                    raise ValueError('wrong pivot signs')
                na ^= bit
                pb ^= bit
            positive, negative = pa | pb, na | nb
        else:
            raise ValueError('unknown proof rule')
        if positive & negative:
            raise ValueError('tautological proof row')
        masks.append((positive, negative))
    return masks
