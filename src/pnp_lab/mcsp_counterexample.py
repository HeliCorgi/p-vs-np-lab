"""Explicit finite circuit synthesis with retained counterexamples and gate values.

No synthesis oracle, truth-table deduplication, or polynomial-time claim is used.
Catalogue construction is exhaustive and its work and space are reported.
"""

from dataclasses import dataclass
from itertools import combinations_with_replacement


@dataclass
class CircuitCatalog:
    n: int
    budget: int
    nodes: list[tuple[str, int, int]]
    construction: dict

    @property
    def gate_count(self):
        return len(self.nodes) - self.n - 2

    def witness(self, root):
        """Export the reachable DAG, including its internal sharing."""
        needed = set()

        def visit(node):
            if node < self.n + 2 or node in needed:
                return
            needed.add(node)
            op, a, b = self.nodes[node]
            visit(a)
            if op != 'NOT':
                visit(b)

        visit(root)
        mapping = {i: i for i in range(self.n + 2)}
        gates = []
        for node in sorted(needed):
            op, a, b = self.nodes[node]
            args = [mapping[a]] if op == 'NOT' else [mapping[a], mapping[b]]
            mapping[node] = self.n + 2 + len(gates)
            gates.append([op, args])
        assert len(gates) <= self.budget
        return {'n': self.n, 'gates': gates, 'output': mapping[root]}


def stream_catalog(n, budget):
    if n < 1 or budget < 0:
        raise ValueError('Require n >= 1 and budget >= 0')
    nodes = [('CONST', 0, 0), ('CONST', 1, 0)]
    nodes += [('INPUT', i, 0) for i in range(n)]
    ledger = {
        'transition_attempts': 0, 'state_insert_attempts': 0,
        'state_records_created': 0, 'peak_frontier_states': 1, 'layers': [],
        'candidate_roots': len(nodes), 'shared_gate_nodes': 0, 'complete': False,
        'uses_target_table': False, 'uses_semantic_deduplication': False,
    }
    catalog = CircuitCatalog(n, budget, nodes, ledger)

    def roots():
        base = tuple(range(n + 2))
        intern, states = {}, {()}
        yield from base
        for depth in range(1, budget + 1):
            completed_states = ledger['state_records_created']
            following = set()
            for state in sorted(states):
                available = base + state
                choices = [('NOT', a, -1) for a in available]
                for a, b in combinations_with_replacement(available, 2):
                    choices.extend((('AND', a, b), ('OR', a, b)))
                for key in choices:
                    ledger['transition_attempts'] += 1
                    node = intern.get(key)
                    new = node is None
                    if new:
                        node = len(nodes)
                        intern[key] = node
                        nodes.append(key)
                        ledger['candidate_roots'] = len(nodes)
                        ledger['shared_gate_nodes'] = len(intern)
                    if node in state:
                        continue
                    ledger['state_insert_attempts'] += 1
                    following.add(tuple(sorted((*state, node))))
                    ledger['state_records_created'] = completed_states + len(following)
                    ledger['peak_frontier_states'] = max(ledger['peak_frontier_states'],
                                                         len(states) + len(following))
                    if new:
                        yield node
            states = following
            ledger['layers'].append({'budget': depth, 'states': len(states), 'gates': len(intern)})
        ledger['complete'] = True

    return catalog, roots()


def build_catalog(n, budget):
    catalog, roots = stream_catalog(n, budget)
    for _ in roots:
        pass
    assert catalog.construction['complete']
    return catalog


def search(catalog, target, mode='samples_and_gates', *, roots=None):
    """Return a witness, or NO only after visiting the complete catalogue.

    Modes retain nothing across candidates, retain counterexamples only, or
    retain counterexamples plus values of shared gates. All use the same roots.
    """
    if mode not in ('fresh', 'samples', 'samples_and_gates'):
        raise ValueError('Unknown mode')
    n, nodes = catalog.n, catalog.nodes
    rows = 1 << n
    if not 0 <= target < 1 << rows:
        raise ValueError('Invalid truth table')
    packed_target = target.to_bytes((rows + 7) // 8, 'little')
    retain_samples = mode != 'fresh'
    retain_gates = mode == 'samples_and_gates'
    examples, example_set = [], set()
    values, target_cache = {}, {}
    stats = dict(candidate_visits=0, sample_checks=0, verification_checks=0,
                 verification_slots=0, cache_lookups=0, cache_hits=0,
                 gate_evaluations=0, input_evaluations=0, constant_evaluations=0,
                 target_lookups=0, target_reads=0, counterexamples=0,
                 peak_value_cache=0, row_root_checks=0,
                 input_bits_loaded=rows, input_bytes=len(packed_target))

    def target_bit(row):
        stats['target_lookups'] += 1
        if row not in target_cache:
            # This is a random-access explicit table, not a compressed oracle.
            target_cache[row] = bool(packed_target[row // 8] >> (row % 8) & 1)
            stats['target_reads'] += 1
        return target_cache[row]

    def evaluate(node, row, memo):
        stats['cache_lookups'] += 1
        key = (row, node)
        if key in memo:
            stats['cache_hits'] += 1
            return memo[key]
        op, a, b = nodes[node]
        if op == 'CONST':
            stats['constant_evaluations'] += 1
            result = bool(a)
        elif op == 'INPUT':
            stats['input_evaluations'] += 1
            result = bool(row >> (n - 1 - a) & 1)
        else:
            left = evaluate(a, row, memo)
            # Always evaluate both children; gate counts do not depend on
            # Python short-circuit evaluation of Boolean expressions.
            right = evaluate(b, row, memo) if op != 'NOT' else False
            stats['gate_evaluations'] += 1
            result = not left if op == 'NOT' else left and right if op == 'AND' else left or right
        memo[key] = result
        stats['peak_value_cache'] = max(stats['peak_value_cache'], len(memo))
        return result

    def agrees(root, row):
        stats['row_root_checks'] += 1
        memo = values if retain_gates else {}
        return evaluate(root, row, memo) == target_bit(row)

    answer = None
    for root in (range(len(nodes)) if roots is None else roots):
        if root != stats['candidate_visits'] or not 0 <= root < len(nodes):
            raise ValueError('Roots must enumerate the catalogue in creation order')
        stats['candidate_visits'] += 1
        rejected = False
        if retain_samples:
            for row in reversed(examples):
                stats['sample_checks'] += 1
                if not agrees(root, row):
                    rejected = True
                    break
        if rejected:
            continue
        for row in range(rows):
            stats['verification_slots'] += 1
            if retain_samples and row in example_set:
                continue
            stats['verification_checks'] += 1
            if not agrees(root, row):
                stats['counterexamples'] += 1
                if retain_samples:
                    assert row not in example_set
                    example_set.add(row)
                    examples.append(row)
                rejected = True
                break
        if not rejected:
            answer = root
            break
    stats['work_units'] = sum(stats[key] for key in (
        'candidate_visits', 'sample_checks', 'verification_slots',
        'cache_lookups', 'gate_evaluations', 'input_evaluations',
        'constant_evaluations', 'target_lookups', 'target_reads', 'counterexamples',
        'input_bits_loaded'))
    stats['retained_examples'] = len(examples)
    if answer is None and (not catalog.construction['complete']
                           or stats['candidate_visits'] != len(nodes)):
        raise ValueError('Incomplete enumeration cannot certify NO')
    assert stats['row_root_checks'] <= rows * stats['candidate_visits']
    if retain_samples:
        assert len(examples) <= rows
    if retain_gates:
        assert stats['gate_evaluations'] <= rows * catalog.gate_count
        assert stats['peak_value_cache'] <= rows * len(nodes)
    return {
        'status': 'YES' if answer is not None else 'NO', 'root': answer,
        'witness': catalog.witness(answer) if answer is not None else None,
        'counterexample_rows': examples, 'metrics': stats,
        'no_scope': 'NO requires completed exhaustive enumeration for the stated n and gate budget',
    }


def search_lazy(n, budget, target):
    catalog, roots = stream_catalog(n, budget)
    try:
        result = search(catalog, target, roots=roots)
    finally:
        roots.close()
    return catalog, result


def witness_table(witness):
    """Independent scalar evaluator for exported ordinary circuits."""
    n, gates, output = witness['n'], witness['gates'], witness['output']
    table = 0
    for row in range(1 << n):
        wires = [False, True] + [bool(row >> (n - 1 - i) & 1) for i in range(n)]
        for op, args in gates:
            if op not in ('NOT', 'AND', 'OR') or len(args) != (1 if op == 'NOT' else 2):
                raise ValueError('Malformed operation')
            if any(not isinstance(a, int) or not 0 <= a < len(wires) for a in args):
                raise ValueError('Invalid wire reference')
            if op == 'NOT':
                value = not wires[args[0]]
            elif op == 'AND':
                value = wires[args[0]] and wires[args[1]]
            else:
                value = wires[args[0]] or wires[args[1]]
            wires.append(value)
        if not isinstance(output, int) or not 0 <= output < len(wires):
            raise ValueError('Invalid output')
        table |= int(wires[output]) << row
    return table
