#!/usr/bin/env python3
"""Finite counterchecks for MCSP update arguments, not a general MCSP solver."""
import argparse
from itertools import combinations_with_replacement
import json
from math import isqrt
from pathlib import Path


class BooleanCircuit:
    """Ordinary counted AND/OR/NOT gates; constants and input wires are free."""

    def __init__(self, n):
        self.n = n
        self.gates = []

    def gate(self, operation, *inputs):
        arity = {'AND': 2, 'OR': 2, 'NOT': 1}[operation]
        if len(inputs) != arity or any(not 0 <= w < self.n + 2 + len(self.gates)
                                      for w in inputs):
            raise ValueError('Invalid gate')
        self.gates.append((operation, inputs))
        return self.n + 1 + len(self.gates)

    def table(self, output):
        answer = []
        for word in range(1 << self.n):
            wires = [False, True] + [bool(word >> (self.n - 1 - j) & 1)
                                     for j in range(self.n)]
            for operation, inputs in self.gates:
                a = wires[inputs[0]]
                if operation == 'NOT':
                    value = not a
                elif operation == 'AND':
                    value = a and wires[inputs[1]]
                else:
                    value = a or wires[inputs[1]]
                wires.append(value)
            answer.append(int(wires[output]))
        return answer

    def point_indicator(self, point):
        literals = [j + 2 if point >> (self.n - 1 - j) & 1
                    else self.gate('NOT', j + 2) for j in range(self.n)]
        result = literals[0]
        for literal in literals[1:]:
            result = self.gate('AND', result, literal)
        return result


def dnf(n, table):
    circuit = BooleanCircuit(n)
    terms = [circuit.point_indicator(i) for i in range(1 << n) if table >> i & 1]
    output = terms[0] if terms else 0
    for term in terms[1:]:
        output = circuit.gate('OR', output, term)
    return circuit, output


def small_circuit_catalog(n, limit):
    """Enumerate DAGs by the set of functions available at each gate count.

    Merging states with equal available truth functions is sound: future
    gates can use any earlier wire, so no other history affects reachability.
    A redundant gate can be removed and its later uses rewired for free.
    """
    mask = (1 << (1 << n)) - 1
    inputs = {0, mask} | {sum(((i >> (n - 1 - j)) & 1) << i for i in range(1 << n))
                              for j in range(n)}
    states, costs, rows = {frozenset(inputs)}, {f: 0 for f in inputs}, []
    for depth in range(1, limit + 1):
        following = set()
        for available in states:
            values = sorted(available)
            possible = {mask ^ a for a in values}
            for a, b in combinations_with_replacement(values, 2):
                possible.update((a & b, a | b))
            for result in possible - available:
                following.add(available | {result})
                costs.setdefault(result, depth)
        states = following
        rows.append(dict(gates=depth, semantic_dag_states=len(states), functions=len(costs)))
    return costs, rows


def audit():
    costs, enumeration = small_circuit_catalog(3, 2)
    prefix = [0, 0, 1, 0, 1]
    encoded = sum(bit << i for i, bit in enumerate(prefix))
    if any(f & 31 == encoded for f in costs):
        raise AssertionError('A circuit of at most two gates matches the prefix')
    first = BooleanCircuit(3)
    f0 = first.gate('AND', first.gate('NOT', 4), first.gate('OR', 2, 3))
    second = BooleanCircuit(3)
    f1 = second.gate('OR', 2, second.gate('AND', 3, second.gate('NOT', 4)))
    tables = [first.table(f0), second.table(f1)]
    if (any(t[:5] != prefix for t in tables) or [t[5] for t in tables] != [0, 1]
            or len(first.gates) != 3 or len(second.gates) != 3):
        raise AssertionError('Flat-minimum counterexample failed')

    patches = []
    for n in (1, 2, 3):
        cases, comparisons, max_added = 0, 0, 0
        for table in range(1 << (1 << n)):
            original, output = dnf(n, table)
            expected = [table >> x & 1 for x in range(1 << n)]
            if original.table(output) != expected:
                raise AssertionError('Independent DNF source construction failed')
            for point in range(1 << n):
                patched = BooleanCircuit(n)
                patched.gates = list(original.gates)
                indicator = patched.point_indicator(point)
                either = patched.gate('OR', output, indicator)
                both = patched.gate('AND', output, indicator)
                out = patched.gate('AND', either, patched.gate('NOT', both))
                added = len(patched.gates) - len(original.gates)
                actual = patched.table(out)
                target = [bit ^ int(x == point) for x, bit in enumerate(expected)]
                if actual != target or added > 2 * n + 3:
                    raise AssertionError('Point repair semantics or gate budget failed')
                max_added = max(max_added, added)
                cases += 1
                comparisons += len(actual)
        patches.append(dict(inputs=n, source_functions=1 << (1 << n),
                            patched_circuits=cases, assignments_compared=comparisons,
                            maximum_added_gates=max_added, proved_added_gate_bound=2 * n + 3))

    reductions = []
    for table in range(16):
        source, gout = dnf(2, table)
        n = max(3, isqrt(len(source.gates) + 1) + 1)
        lifted = BooleanCircuit(n)
        rename = {0: 0, 1: 1, 2: 3, 3: 4}  # first variable is the new control t
        for old, (operation, inputs) in enumerate(source.gates, 4):
            rename[old] = lifted.gate(operation, *(rename[w] for w in inputs))
        output = lifted.gate('AND', lifted.gate('NOT', 2), rename[gout])
        values = lifted.table(output)
        cut = 1 << (n - 1)
        prescribed_valid = not any(values[:cut]) and values[cut] == 0
        if prescribed_valid != (table == 0) or len(lifted.gates) > n * n:
            raise AssertionError('Candidate-validation reduction failed')
        # Regardless of the supplied candidate, the zero circuit repairs the
        # all-zero prefix followed by zero. Verification hardness is not search hardness.
        zero_repairs = not any(lifted.table(0)[:cut + 1])
        if not zero_repairs:
            raise AssertionError('Trivial repair control failed')
        reductions.append(dict(source_truth_table=table, inputs=n, gate_budget=n * n,
                               candidate_gates=len(lifted.gates),
                               prescribed_candidate_valid=prescribed_valid,
                               zero_circuit_is_valid_repair=zero_repairs))

    return dict(all_checks_passed=True,
                flat_minimum=dict(prefix=prefix, prefix_minimum_gates=3,
                                  next_bits=[0, 1], child_minimum_gates=[3, 3],
                                  witness_tables=tables, exhaustive_catalog=enumeration),
                point_repairs=patches, prescribed_candidate_controls=reductions,
                core_lower_bound_proved=False, p_vs_np_resolved=False,
                proof_scope='Finite checks of the paper lemmas in docs/mcsp_update_core.md; no Lean claim')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out-dir', type=Path)
    args = parser.parse_args()
    text = json.dumps(audit(), sort_keys=True, indent=2) + '\n'
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / 'mcsp_update_gate.json').write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
