"""Counterexample refinement with sample-state quotients and safe region cuts.

Equivalence is used only within one fixed sample set. Every refinement
rebuilds the quotient, so a newly distinguished circuit is never lost.
"""

from collections import Counter
from itertools import combinations_with_replacement


def gate_choices(values):
    for a in values:
        yield 'NOT', a, -1
    for a, b in combinations_with_replacement(values, 2):
        yield 'AND', a, b
        yield 'OR', a, b


def gate_value(op, a, b, mask):
    return mask ^ a if op == 'NOT' else a & b if op == 'AND' else a | b


def depth_exclusion(values, target, width, remaining, limit, stats, first_layer=None):
    """True proves no completion; False/None mean reachable/unknown.

    Each depth layer permits unlimited parallel gates. This overapproximates
    every extension with at most `remaining` gates. Hitting the operation cap
    must never be interpreted as exclusion.
    """
    stats['relax_calls'] += 1
    reachable = set(values)
    stats['relax_set_entries'] += len(reachable)
    mask = (1 << width) - 1
    used = 0
    if target in reachable:
        return False
    for depth in range(remaining):
        stats['relax_layers'] += 1
        following = set(reachable)
        stats['relax_set_entries'] += len(reachable)
        for op, a, b in gate_choices(sorted(reachable)):
            if used == limit:
                stats['relax_unknown'] += 1
                return None
            used += 1
            stats['relax_gate_ops'] += 1
            stats['relax_gate_bits'] += width
            value = gate_value(op, a, b, mask)
            if depth == 0 and first_layer is not None:
                first_layer[op, a, b] = value
            stats['relax_insert_attempts'] += 1
            following.add(value)
            if value == target:
                return False
        if following == reachable:
            return True
        reachable = following
    return True


def solve_samples(n, budget, examples, *, relaxation_limit=128):
    """Find a <=budget-gate circuit agreeing with (row, bit) examples.

    A state contains ALL available sample signatures, preserving circuit
    sharing. Deduplicating individual output signatures alone is insufficient.
    """
    if n < 1 or budget < 0 or relaxation_limit < 0:
        raise ValueError('Require positive n and nonnegative budgets')
    examples = tuple(examples)
    if any(not 0 <= row < 1 << n or bit not in (0, 1) for row, bit in examples):
        raise ValueError('Invalid sample')
    if len({row for row, _ in examples}) != len(examples):
        raise ValueError('Sample rows must be distinct')
    width = len(examples)
    mask = (1 << width) - 1
    target = sum(bit << j for j, (_, bit) in enumerate(examples))
    base = [0, mask] + [sum(((row >> (n - 1 - i)) & 1) << j
                           for j, (row, _) in enumerate(examples)) for i in range(n)]
    wire_for = {}
    for wire, value in enumerate(base):
        wire_for.setdefault(value, wire)
    initial = tuple(sorted(wire_for))
    stats = Counter(base_signature_bits=(n + 2) * width, target_signature_bits=width,
                    states_created=1, state_key_entries=len(initial), states_expanded=0,
                    transition_attempts=0, signature_gate_bits=0,
                    reused_transition_values=0,
                    redundant_value_cuts=0, equivalent_state_cuts=0,
                    budget_leaf_cuts=0, infeasible_region_cuts=0,
                    relax_calls=0, relax_layers=0, relax_gate_ops=0, relax_gate_bits=0,
                    relax_set_entries=0, relax_insert_attempts=0, relax_unknown=0,
                    witness_gates_built=0, peak_frontier_states=1)
    # Record: (available signatures, parent index, appended gate).
    records = [(initial, None, None)]
    seen = {initial: 0}
    cuts = []

    def finish(index):
        witness = None
        if index is not None:
            path = []
            while records[index][1] is not None:
                _, parent, gate = records[index]
                path.append(gate)
                index = parent
            wires = dict(wire_for)
            gates = []
            for op, a, b, value in reversed(path):
                args = [wires[a]] if op == 'NOT' else [wires[a], wires[b]]
                wires[value] = n + 2 + len(gates)
                gates.append([op, args])
            witness = {'n': n, 'gates': gates, 'output': wires[target]}
            stats['witness_gates_built'] = len(gates)
        # Record counts/bit widths, not an exact Python execution-time model.
        stats['work_units'] = sum(stats[key] for key in (
            'base_signature_bits', 'target_signature_bits', 'states_created',
            'state_key_entries', 'states_expanded', 'transition_attempts',
            'signature_gate_bits', 'relax_calls', 'relax_layers', 'relax_gate_ops',
            'relax_gate_bits', 'relax_set_entries', 'relax_insert_attempts',
            'witness_gates_built'))
        return {'status': 'YES' if witness is not None else 'NO', 'witness': witness,
                'sample_count': width, 'target_signature': target,
                'metrics': dict(stats), 'pruned_regions': cuts,
                'complete_sample_decision': True}

    if target in wire_for:
        return finish(0)
    cursor = 0
    while cursor < len(records):
        index = cursor
        values, _, _ = records[index]
        cursor += 1
        stats['states_expanded'] += 1
        remaining = budget - (len(values) - len(initial))
        if remaining == 0:
            stats['budget_leaf_cuts'] += 1
            continue
        first_layer = {}
        if relaxation_limit:
            before = stats['relax_gate_ops']
            excluded = depth_exclusion(values, target, width, remaining,
                                       relaxation_limit, stats, first_layer)
            if excluded is True:
                stats['infeasible_region_cuts'] += 1
                cuts.append({'available': list(values), 'remaining': remaining,
                             'relax_gate_ops': stats['relax_gate_ops'] - before})
                continue  # No child state or concrete suffix is generated.
        for op, a, b in gate_choices(values):
            stats['transition_attempts'] += 1
            if (op, a, b) in first_layer:
                value = first_layer[op, a, b]
                stats['reused_transition_values'] += 1
            else:
                stats['signature_gate_bits'] += width
                value = gate_value(op, a, b, mask)
            if value in values:
                stats['redundant_value_cuts'] += 1
                continue  # This gate can be replaced by an available wire on the samples.
            child = tuple(sorted((*values, value)))
            stats['state_key_entries'] += len(child)
            if child in seen:
                stats['equivalent_state_cuts'] += 1
                continue  # The representative already covers every sample continuation.
            child_index = len(records)
            seen[child] = child_index
            records.append((child, index, (op, a, b, value)))
            stats['states_created'] += 1
            stats['peak_frontier_states'] = max(stats['peak_frontier_states'],
                                                len(records) - cursor)
            if value == target:
                return finish(child_index)
    return finish(None)


def first_mismatch(witness, packed_target, stats):
    """Scalar full verifier, charging every evaluated gate and input wire."""
    n, gates, output = witness['n'], witness['gates'], witness['output']
    for row in range(1 << n):
        stats['verification_rows'] += 1
        wires = [False, True] + [bool(row >> (n - 1 - i) & 1) for i in range(n)]
        stats['verification_base_values'] += n + 2
        for op, args in gates:
            left = wires[args[0]]
            right = wires[args[1]] if op != 'NOT' else False
            wires.append(not left if op == 'NOT' else left and right if op == 'AND' else left or right)
            stats['verification_gate_ops'] += 1
        stats['target_reads'] += 1
        bit = packed_target[row // 8] >> (row % 8) & 1
        if wires[output] != bit:
            return row, bit
    return None


def search_regions(n, budget, target, *, relaxation_limit=128):
    """CEGIS with a freshly constructed sound quotient after each new row."""
    if n < 1 or budget < 0 or relaxation_limit < 0:
        raise ValueError('Require positive n and nonnegative budgets')
    rows = 1 << n
    if not 0 <= target < 1 << rows:
        raise ValueError('Invalid truth table')
    packed = target.to_bytes((rows + 7) // 8, 'little')
    examples, example_rows, iterations = [], set(), []
    stats = Counter(input_bits_loaded=rows, synthesis_rounds=0,
                    concrete_candidates=0, verification_rows=0,
                    verification_base_values=0, verification_gate_ops=0,
                    target_reads=0, counterexamples=0, synthesis_work_units=0,
                    peak_sample_states=0, peak_frontier_states=0)
    while True:
        result = solve_samples(n, budget, examples, relaxation_limit=relaxation_limit)
        stats['synthesis_rounds'] += 1
        stats['synthesis_work_units'] += result['metrics']['work_units']
        stats['peak_sample_states'] = max(stats['peak_sample_states'],
                                          result['metrics']['states_created'])
        stats['peak_frontier_states'] = max(stats['peak_frontier_states'],
                                            result['metrics']['peak_frontier_states'])
        # Every rebuilding cost is included; no equivalence cut survives refinement.
        for key in ('transition_attempts', 'signature_gate_bits', 'states_created',
                    'state_key_entries', 'redundant_value_cuts', 'equivalent_state_cuts',
                    'infeasible_region_cuts', 'relax_gate_ops', 'relax_gate_bits',
                    'relax_unknown', 'witness_gates_built', 'reused_transition_values'):
            stats[key] += result['metrics'][key]
        result['examples'] = [list(pair) for pair in examples]
        iterations.append(result)
        if result['status'] == 'NO':
            status, witness = 'NO', None
            break
        stats['concrete_candidates'] += 1
        mismatch = first_mismatch(result['witness'], packed, stats)
        if mismatch is None:
            status, witness = 'YES', result['witness']
            break
        row, bit = mismatch
        if row in example_rows:
            raise AssertionError('Synthesis returned a circuit violating an existing sample')
        example_rows.add(row)
        examples.append((row, bit))
        stats['counterexamples'] += 1
    stats['work_units'] = sum(stats[key] for key in (
        'input_bits_loaded', 'synthesis_rounds', 'synthesis_work_units',
        'concrete_candidates', 'verification_rows', 'verification_base_values',
        'verification_gate_ops', 'target_reads', 'counterexamples'))
    assert len(examples) <= rows and stats['synthesis_rounds'] <= rows + 1
    return {'status': status, 'witness': witness, 'examples': [list(pair) for pair in examples],
            'metrics': dict(stats), 'iterations': iterations,
            'no_scope': 'NO proves that the retained samples have no circuit within this gate budget'}
