"""Fixed-size universal-circuit constraints with incremental evidence.

Construction and evidence propagation are polynomial in the explicit table
length and gate budget. Exact extraction is implemented, but its decision
tree has no general polynomial bound. A work cap returns UNKNOWN, never NO.
"""

from collections import Counter
from itertools import combinations


class _Limit(Exception):
    pass


class _Meter:
    def __init__(self, cap=None):
        self.cap = cap
        self.stats = Counter(work_units=0)

    def add(self, key, amount=1):
        if self.cap is not None and self.stats['work_units'] + amount > self.cap:
            raise _Limit
        self.stats[key] += amount
        self.stats['work_units'] += amount


def _neg(literal):
    return not literal if type(literal) is bool else -literal


class FixedCircuitSpace:
    """All <=s-gate AND/OR/NOT circuits encoded in one immutable CNF.

    Exactly s slots are used; unused gates pad smaller circuits. The output
    may select any input, constant or gate. Each possible truth-table row
    already has its own evaluation variables before evidence is supplied.
    """

    def __init__(self, n, budget):
        if n < 1 or budget < 0:
            raise ValueError('Require n >= 1 and budget >= 0')
        self.n, self.budget, self.rows = n, budget, 1 << n
        self.variables = 0
        clauses = []
        self.compile = Counter(clause_attempts=0, literal_slots_processed=0)

        def variable():
            self.variables += 1
            return self.variables

        def clause(*literals):
            self.compile['clause_attempts'] += 1
            self.compile['literal_slots_processed'] += len(literals)
            remaining = set()
            for literal in literals:
                if type(literal) is bool:
                    if literal:
                        return
                    continue
                if -literal in remaining:
                    return
                remaining.add(literal)
            clauses.append(tuple(sorted(remaining, key=lambda x: (abs(x), x))))

        def one_hot(size):
            choices = tuple(variable() for _ in range(size))
            clause(*choices)
            for a, b in combinations(choices, 2):
                clause(-a, -b)
            return choices

        def mux(choices, wires, result):
            for choice, wire in zip(choices, wires):
                clause(-choice, -result, wire)
                clause(-choice, result, _neg(wire))

        self.gates = []
        for i in range(budget):
            count = n + 2 + i
            ops, left, right = one_hot(3), one_hot(count), one_hot(count)
            # NOT ignores its second argument. AND/OR are commutative.
            clause(-ops[0], right[0])
            for a in range(count):
                for b in range(a):
                    for op in ops[1:]:
                        clause(-op, -left[a], -right[b])
            self.gates.append((ops, left, right))
        self.gates = tuple(self.gates)
        self.output_choices = one_hot(n + 2 + budget)
        self.groups = (self.output_choices,) + tuple(group for gate in reversed(self.gates) for group in gate)
        self.row_aux, outputs = [], []
        for row in range(self.rows):
            wires = [False, True] + [bool(row >> (n - 1 - i) & 1) for i in range(n)]
            auxiliary = []
            for ops, left, right in self.gates:
                a, b, z = variable(), variable(), variable()
                mux(left, wires, a)
                mux(right, wires, b)
                clause(-ops[0], z, a)
                clause(-ops[0], -z, -a)
                clause(-ops[1], -a, -b, z)
                clause(-ops[1], a, -z)
                clause(-ops[1], b, -z)
                clause(-ops[2], a, b, -z)
                clause(-ops[2], -a, z)
                clause(-ops[2], -b, z)
                auxiliary.append((a, b, z))
                wires.append(z)
            output = variable()
            mux(self.output_choices, wires, output)
            outputs.append(output)
            self.row_aux.append(tuple(auxiliary))
        self.row_aux, self.outputs = tuple(self.row_aux), tuple(outputs)
        self.clauses = tuple(clauses)
        occurrences = {}
        for index, literals in enumerate(self.clauses):
            for literal in literals:
                occurrences.setdefault(literal, []).append(index)
        self.occurrences = {literal: tuple(indices) for literal, indices in occurrences.items()}
        self.literal_slots = sum(map(len, self.clauses))
        self.root_inspection_bound = sum(len(clause) ** 2 for clause in self.clauses)
        self.compile.update(variables=self.variables, clauses=len(self.clauses),
                            stored_literal_slots=self.literal_slots, occurrence_slots=self.literal_slots,
                            row_slots=self.rows, program_groups=len(self.groups),
                            program_variables=sum(map(len, self.groups)), bound_clause_scans=len(self.clauses))
        self.compile['work_units'] = sum(self.compile.values())
        self.shape = (self.variables, len(self.clauses), self.literal_slots, self.rows,
                      tuple(map(len, self.groups)))
        self.evidence = [0] * self.rows
        self.root = [0] * (self.variables + 1)
        self.root_trail = []
        self.update_meter = _Meter()
        self.inconsistent = False
        for literals in self.clauses:
            if not literals:
                self.inconsistent = True
            elif len(literals) == 1 and not self._assign(self.root, self.root_trail, literals[0], self.update_meter):
                self.inconsistent = True
        if not self.inconsistent:
            self.inconsistent = not self._propagate(self.root, self.root_trail, 0, self.update_meter)

    @staticmethod
    def _assign(values, trail, literal, meter):
        meter.add('assignment_checks')
        variable, value = abs(literal), 1 if literal > 0 else -1
        if values[variable]:
            return values[variable] == value
        values[variable] = value
        trail.append(literal)
        meter.add('assigned_variables')
        return True

    def _propagate(self, values, trail, cursor, meter):
        while cursor < len(trail):
            literal = trail[cursor]
            cursor += 1
            meter.add('propagation_queue_visits')
            for index in self.occurrences.get(-literal, ()):
                meter.add('clause_visits')
                satisfied, unassigned, unit = False, 0, None
                for lit in self.clauses[index]:
                    meter.add('literal_inspections')
                    value = values[abs(lit)]
                    if value == (1 if lit > 0 else -1):
                        satisfied = True
                        break
                    if not value:
                        unassigned += 1
                        unit = lit
                if satisfied:
                    continue
                if not unassigned:
                    meter.add('conflicts')
                    return False
                if unassigned == 1 and not self._assign(values, trail, unit, meter):
                    meter.add('conflicts')
                    return False
        return True

    def add_example(self, row, bit):
        if not 0 <= row < self.rows or bit not in (0, 1):
            raise ValueError('Invalid example')
        self.update_meter.add('example_requests')
        value = 1 if bit else -1
        if self.evidence[row]:
            if self.evidence[row] != value:
                self.inconsistent = True
            return not self.inconsistent
        self.evidence[row] = value
        self.update_meter.add('evidence_writes')
        if self.inconsistent:
            return False
        cursor = len(self.root_trail)
        literal = self.outputs[row] * value
        self.inconsistent = (not self._assign(self.root, self.root_trail, literal, self.update_meter)
                             or not self._propagate(self.root, self.root_trail, cursor, self.update_meter))
        return not self.inconsistent

    def residual_choices(self, meter=None):
        """A computable upper bound on remaining program assignments."""
        if self.inconsistent:
            return 0
        product = 1
        for group in self.groups:
            if meter is not None:
                meter.add('bound_selector_visits', len(group))
            if not any(self.root[v] == 1 for v in group):
                if meter is not None:
                    meter.add('bound_arithmetic_bits', product.bit_length() + len(group).bit_length())
                product *= sum(self.root[v] == 0 for v in group)
        return product

    def decode(self, values):
        def chosen(group):
            return next(i for i, variable in enumerate(group) if values[variable] == 1)
        gates = []
        for ops, left, right in self.gates:
            op = ('NOT', 'AND', 'OR')[chosen(ops)]
            args = [chosen(left)] if op == 'NOT' else [chosen(left), chosen(right)]
            gates.append([op, args])
        return {'n': self.n, 'gates': gates, 'output': chosen(self.output_choices)}

    def extract(self, *, max_work=500_000):
        """Finite exact group search with polynomial working space.

        No learned-clause database or unbounded proof log is constructed.
        All branches are accounted for; a cap leaves feasibility UNKNOWN.
        """
        if max_work is not None and (type(max_work) is not int or max_work < 0):
            raise ValueError('Invalid work limit')
        meter = _Meter(max_work)
        status, witness, peak_frames, peak_trail = 'UNKNOWN', None, 0, 0
        root_choices = None
        trail, frames = [], []

        def next_options(values):
            def selection(group, order=None):
                meter.add('group_selector_visits', len(group))
                selected = next((i for i, v in enumerate(group) if values[v] == 1), None)
                if selected is not None:
                    return selected, None
                indices = range(len(group)) if order is None else order
                return None, tuple(group[i] for i in indices if values[group[i]] == 0)

            output, options = selection(self.output_choices)
            if options is not None:
                return options
            pending, visited = [output], set()
            while pending:
                wire = pending.pop()
                if wire < self.n + 2 or wire in visited:
                    continue
                visited.add(wire)
                meter.add('cone_gate_visits')
                ops, left, right = self.gates[wire - self.n - 2]
                op, options = selection(ops, (1, 2, 0))
                if options is not None:
                    return options
                a, options = selection(left)
                if options is not None:
                    return options
                pending.append(a)
                if op:
                    b, options = selection(right)
                    if options is not None:
                        return options
                    pending.append(b)
            return None

        def accept(values, trail):
            # All gates reachable from the selected output are determined.
            # Unused slots can be fixed to NOT(False), without enumerating them.
            cursor = len(trail)
            for gate in self.gates:
                for group in gate:
                    meter.add('padding_selector_visits', len(group))
                    if not any(values[v] == 1 for v in group):
                        if not self._assign(values, trail, group[0], meter):
                            return None
            if not self._propagate(values, trail, cursor, meter):
                return None
            # A completed program forces every evaluation wire. Verify the CNF
            # explicitly as well, instead of treating no decision as a witness.
            for literals in self.clauses:
                meter.add('validation_literal_slots', len(literals))
                if not any(values[abs(lit)] == (1 if lit > 0 else -1) for lit in literals):
                    raise AssertionError('Incomplete or invalid model')
            meter.add('witness_output_slots', 3 * self.budget + 1)
            return self.decode(values)

        try:
            root_choices = self.residual_choices(meter)
            if self.inconsistent:
                meter.add('root_conflict_checks')
                status = 'NO'
            else:
                meter.add('working_copy_slots', len(self.root) + len(self.root_trail))
                values, trail = list(self.root), list(self.root_trail)
                peak_trail = len(trail)
                options = next_options(values)
                if options is None:
                    witness = accept(values, trail)
                    peak_trail = max(peak_trail, len(trail))
                    status = 'YES' if witness is not None else 'NO'
                else:
                    # Frame: remaining choices, next index, trail checkpoint.
                    frames = [[options, 0, len(trail)]]
                    while frames:
                        peak_frames = max(peak_frames, len(frames))
                        choices, position, checkpoint = frames[-1]
                        while len(trail) > checkpoint:
                            meter.add('trail_undo')
                            values[abs(trail.pop())] = 0
                        if position == len(choices):
                            frames.pop()
                            continue
                        frames[-1][1] += 1
                        meter.add('decisions')
                        if not self._assign(values, trail, choices[position], meter):
                            continue
                        consistent = self._propagate(values, trail, checkpoint, meter)
                        peak_trail = max(peak_trail, len(trail))
                        if not consistent:
                            continue
                        options = next_options(values)
                        if options is None:
                            witness = accept(values, trail)
                            peak_trail = max(peak_trail, len(trail))
                            if witness is not None:
                                status = 'YES'
                                break
                            continue
                        frames.append([options, 0, len(trail)])
                    else:
                        status = 'NO'
        except _Limit:
            peak_trail = max(peak_trail, len(trail))
            peak_frames = max(peak_frames, len(frames))
            status, witness = 'UNKNOWN', None
        return {'status': status, 'witness': witness, 'metrics': dict(meter.stats),
                'root_program_choice_bound': root_choices,
                'peak_decision_frames': peak_frames, 'peak_trail_slots': peak_trail,
                'scope': 'NO requires root contradiction or complete search; resource exhaustion is UNKNOWN'}


def search_fixed(n, budget, target, *, max_work_per_extract=500_000):
    """Refine only evidence slots; never rebuild the candidate formula."""
    from .mcsp_region_search import first_mismatch

    if n < 1 or budget < 0 or not 0 <= target < 1 << (1 << n):
        raise ValueError('Invalid circuit task')
    space = FixedCircuitSpace(n, budget)
    packed = target.to_bytes((space.rows + 7) // 8, 'little')
    verification = Counter(input_bits_loaded=space.rows)
    iterations, examples = [], []
    while True:
        result = space.extract(max_work=max_work_per_extract)
        result['sample_count'] = len(examples)
        result['root_assigned_variables'] = len(space.root_trail)
        iterations.append(result)
        if result['status'] != 'YES':
            break
        mismatch = first_mismatch(result['witness'], packed, verification)
        if mismatch is None:
            break
        row, bit = mismatch
        if space.evidence[row]:
            raise AssertionError('A returned circuit violates retained evidence')
        examples.append([row, bit])
        space.add_example(row, bit)
    assert len(iterations) <= space.rows + 1
    assert len(space.root_trail) <= space.variables
    assert space.update_meter.stats['literal_inspections'] <= space.root_inspection_bound
    assert space.update_meter.stats['clause_visits'] <= space.literal_slots
    final_shape = (space.variables, len(space.clauses), sum(map(len, space.clauses)),
                   len(space.evidence), tuple(map(len, space.groups)))
    assert final_shape == space.shape
    extraction_work = sum(r['metrics']['work_units'] for r in iterations)
    verification_work = sum(verification.values())
    return {'status': result['status'], 'witness': result['witness'], 'examples': examples,
            'iterations': iterations, 'shape': list(space.shape[:4]), 'shape_unchanged': True,
            'compile': dict(space.compile), 'update': dict(space.update_meter.stats),
            'root_literal_inspection_bound_all_updates': space.root_inspection_bound,
            'verification': dict(verification), 'extraction_work_units': extraction_work,
            'accounted_work_units': space.compile['work_units'] + space.update_meter.stats['work_units']
            + extraction_work + verification_work,
            'general_polynomial_extraction_bound': False}
