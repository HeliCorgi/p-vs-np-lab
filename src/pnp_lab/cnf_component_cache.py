"""Exact residual-CNF sharing, independent components, and explicit budgets.

Dense variable renaming is only a sufficient syntactic equivalence test.
Cached answers belong to the entire normalized residual formula, never to
an assignment prefix with omitted conditions. No polynomial cache-size bound
is assumed. Completed entries survive a query timeout; incomplete ones do not.
"""

from collections import Counter


class _Stop(Exception):
    pass


class _Meter:
    def __init__(self, cap):
        self.cap = cap
        self.stats = Counter(work_units=0, calls=0, computed_states=0, completed_states=0,
                             cache_hits=0, nontrivial_cache_hits=0, cache_inserts=0,
                             cross_query_cache_hits=0,
                             cache_capacity_skips=0, decisions=0, component_splits=0,
                             components_solved=0, peak_depth=0)

    def charge(self, key, amount=1):
        if self.cap is not None and self.stats['work_units'] + amount > self.cap:
            raise _Stop
        self.stats[key] += amount
        self.stats['work_units'] += amount


class ComponentSolver:
    def __init__(self, *, cache=True, split=True, max_cache_cells=250_000):
        if max_cache_cells is not None and (type(max_cache_cells) is not int or max_cache_cells < 0):
            raise ValueError('Invalid cache capacity')
        self.use_cache, self.split = cache, split
        self.max_cache_cells = max_cache_cells
        self.cache, self.cache_cells = {}, 0
        self.query_index = 0

    @staticmethod
    def _restrict(clauses, assignment, meter):
        result = []
        for clause in clauses:
            residual, satisfied = [], False
            for literal in clause:
                meter.charge('restriction_literal_visits')
                value = assignment.get(abs(literal))
                if value is None:
                    residual.append(literal)
                elif value == (literal > 0):
                    satisfied = True
                    break
            if not satisfied:
                result.append(tuple(residual))
        return tuple(result)

    @staticmethod
    def _normalize(clauses, meter):
        cleaned = set()
        for clause in clauses:
            meter.charge('normalization_literal_visits', len(clause))
            literals = set(clause)
            if any(-literal in literals for literal in literals):
                continue
            if not literals:
                return ((),), ()
            cleaned.add(tuple(sorted(literals, key=lambda x: (abs(x), x))))
        variables = tuple(sorted({abs(literal) for clause in cleaned for literal in clause}))
        meter.charge('normalization_variable_slots', len(variables))
        ranks = {variable: i + 1 for i, variable in enumerate(variables)}
        key = tuple(sorted(tuple(ranks[abs(lit)] if lit > 0 else -ranks[abs(lit)]
                                 for lit in clause) for clause in cleaned))
        return key, variables

    @staticmethod
    def _components(clauses, meter):
        parent = {}

        def find(variable):
            parent.setdefault(variable, variable)
            while parent[variable] != variable:
                meter.charge('component_find_steps')
                parent[variable] = parent[parent[variable]]
                variable = parent[variable]
            return variable

        for clause in clauses:
            anchor = abs(clause[0])
            for literal in clause:
                meter.charge('component_literal_visits')
                a, b = find(anchor), find(abs(literal))
                if a != b:
                    parent[max(a, b)] = min(a, b)
        groups = {}
        for clause in clauses:
            groups.setdefault(find(abs(clause[0])), []).append(clause)
        return [tuple(groups[root]) for root in sorted(groups)]

    def solve(self, clauses, *, assumptions=None, max_work=500_000, decision_order=None):
        if max_work is not None and (type(max_work) is not int or max_work < 0):
            raise ValueError('Invalid work cap')
        clauses = tuple(tuple(clause) for clause in clauses)
        if any(type(lit) is not int or lit == 0 for clause in clauses for lit in clause):
            raise ValueError('CNF literals must be nonzero integers')
        initial = dict(assumptions or {})
        if any(type(v) is not int or v < 1 or type(bit) is not bool for v, bit in initial.items()):
            raise ValueError('Assumptions map positive variables to Boolean values')
        meter = _Meter(max_work)
        self.query_index += 1
        before = self.cache_cells

        def visit(formula, context, depth=0):
            meter.stats['peak_depth'] = max(meter.stats['peak_depth'], depth)
            meter.charge('calls')
            key, variables = self._normalize(formula, meter)
            key_cells = len(key) + sum(map(len, key)) + 3
            meter.charge('key_cells_examined', key_cells)

            def lift(answer):
                if answer is None:
                    return None
                meter.charge('model_remap_slots', len(variables))
                return dict(zip(variables, answer))

            if self.use_cache and key in self.cache:
                meter.charge('cache_hits')
                meter.stats['nontrivial_cache_hits'] += len(key) > 1 and len(variables) > 1
                packed, born = self.cache[key]
                meter.stats['cross_query_cache_hits'] += born < self.query_index
                return lift(packed)
            meter.charge('computed_states')
            residual = tuple(tuple(variables[abs(lit) - 1] * (1 if lit > 0 else -1)
                                   for lit in clause) for clause in key)
            assigned = {}
            answer = None
            while True:
                units = {}
                conflict = False
                for clause in residual:
                    meter.charge('propagation_clause_visits')
                    if not clause:
                        conflict = True
                        break
                    if len(clause) == 1:
                        literal = clause[0]
                        variable, bit = abs(literal), literal > 0
                        if variable in units and units[variable] != bit:
                            conflict = True
                            break
                        units[variable] = bit
                if conflict:
                    break
                if not residual:
                    answer = assigned
                    break
                if units:
                    assigned.update(units)
                    meter.charge('unit_assignments', len(units))
                    residual = self._restrict(residual, units, meter)
                    continue
                meter.charge('context_copy_slots', len(context) + len(assigned))
                child_context = dict(context)
                child_context.update(assigned)
                components = self._components(residual, meter) if self.split else [residual]
                if len(components) > 1:
                    meter.charge('component_splits')
                    combined = dict(assigned)
                    for component in components:
                        meter.charge('components_solved')
                        child = visit(component, child_context, depth + 1)
                        if child is None:
                            break
                        combined.update(child)
                    else:
                        answer = combined
                    break
                branches = None
                if decision_order is not None:
                    clause_set = set(residual)
                    meter.charge('branch_clause_cells', len(residual) + sum(map(len, residual)))
                    for group in decision_order(child_context, meter):
                        meter.charge('preferred_group_visits', len(group))
                        if any(child_context.get(v) is True for v in group):
                            continue
                        choices = tuple(v for v in group if v not in child_context)
                        # The actual residual must contain this disjunction.
                        # Metadata only chooses a branching order, never a constraint.
                        if choices and tuple(sorted(choices)) in clause_set:
                            branches = [{v: True} for v in choices]
                            break
                if branches is None:
                    frequency = Counter()
                    for clause in residual:
                        meter.charge('branch_literal_visits', len(clause))
                        frequency.update(map(abs, clause))
                    variable = min(frequency, key=lambda v: (-frequency[v], v))
                    branches = [{variable: True}, {variable: False}]
                meter.charge('decisions')
                for choice in branches:
                    child_formula = self._restrict(residual, choice, meter)
                    branch_context = dict(child_context)
                    branch_context.update(choice)
                    meter.charge('context_copy_slots', len(branch_context))
                    child = visit(child_formula, branch_context, depth + 1)
                    if child is not None:
                        answer = dict(assigned)
                        answer.update(child)
                        answer.update(choice)
                        break
                break
            # A successful partial assignment extends with False on absent
            # variables: every residual clause is already satisfied.
            packed = None if answer is None else tuple(answer.get(v, False) for v in variables)
            meter.charge('completed_states')
            if self.use_cache:
                cells = key_cells + (len(packed) if packed is not None else 0)
                if self.max_cache_cells is None or self.cache_cells + cells <= self.max_cache_cells:
                    meter.charge('cache_cells_written', cells)
                    self.cache[key] = packed, self.query_index
                    self.cache_cells += cells
                    meter.stats['cache_inserts'] += 1
                else:
                    meter.charge('cache_capacity_skips')
            return lift(packed)

        status, model, reason = 'UNKNOWN', None, None
        try:
            meter.charge('input_literal_slots', sum(map(len, clauses)))
            meter.charge('input_clause_slots', len(clauses))
            meter.charge('assumption_slots', len(initial))
            residual = self._restrict(clauses, initial, meter)
            result = visit(residual, initial)
            if result is None:
                status = 'NO'
            else:
                result.update(initial)
                for clause in clauses:
                    meter.charge('validation_literal_slots', len(clause))
                    if not any(result.get(abs(lit), False) == (lit > 0) for lit in clause):
                        raise AssertionError('Invalid cached or composed model')
                model, status = result, 'YES'
        except _Stop:
            reason = 'work_limit'
        except RecursionError:
            reason = 'recursion_limit'
        return {'status': status, 'model': model, 'reason': reason, 'metrics': dict(meter.stats),
                'cache_cells_before': before, 'cache_cells_after': self.cache_cells,
                'cache_entries_after': len(self.cache), 'cache_enabled': self.use_cache,
                'scope': 'Only completed exact residuals are cached; UNKNOWN never proves NO'}


def search_shared(n, budget, target, *, cache=True, max_work_per_extract=500_000,
                  max_cache_cells=250_000):
    from .mcsp_fixed_constraints import FixedCircuitSpace
    from .mcsp_region_search import first_mismatch

    if n < 1 or budget < 0 or not 0 <= target < 1 << (1 << n):
        raise ValueError('Invalid circuit task')
    space = FixedCircuitSpace(n, budget)
    solver = ComponentSolver(cache=cache, max_cache_cells=max_cache_cells)

    def circuit_order(context, meter):
        order = [space.output_choices]
        meter.charge('circuit_selector_visits', len(space.output_choices))
        output = next((i for i, v in enumerate(space.output_choices) if context.get(v) is True), None)
        pending, visited = ([] if output is None else [output]), set()
        while pending:
            wire = pending.pop()
            if wire < n + 2 or wire in visited:
                continue
            visited.add(wire)
            ops, left, right = space.gates[wire - n - 2]
            order.extend(((ops[1], ops[2], ops[0]), left, right))
            for group in (left, right):
                meter.charge('circuit_selector_visits', len(group))
                parent = next((i for i, v in enumerate(group) if context.get(v) is True), None)
                if parent is not None:
                    pending.append(parent)
        order.extend(space.groups)
        return order
    packed = target.to_bytes((space.rows + 7) // 8, 'little')
    verification = Counter(input_bits_loaded=space.rows)
    iterations, examples = [], []
    while True:
        assumptions = {v: bit == 1 for v, bit in enumerate(space.root) if v and bit}
        result = solver.solve(((),) if space.inconsistent else space.clauses,
                              assumptions=assumptions, max_work=max_work_per_extract,
                              decision_order=circuit_order)
        result['sample_count'] = len(examples)
        result['preparation_work_units'] = space.variables + 1
        if result['status'] == 'YES':
            values = [1 if result['model'].get(v, False) else -1 for v in range(space.variables + 1)]
            result['witness'] = space.decode(values)
            result['decode_work_units'] = space.variables + 1 + sum(map(len, space.groups)) + 3*budget + 1
        else:
            result['witness'] = None
            result['decode_work_units'] = 0
        del result['model']
        iterations.append(result)
        if result['status'] != 'YES':
            break
        mismatch = first_mismatch(result['witness'], packed, verification)
        if mismatch is None:
            break
        row, bit = mismatch
        if space.evidence[row]:
            raise AssertionError('Shared extraction violated retained evidence')
        examples.append([row, bit])
        space.add_example(row, bit)
    assert len(iterations) <= space.rows + 1
    return {'status': result['status'], 'witness': result['witness'], 'examples': examples,
            'iterations': iterations, 'compile_work_units': space.compile['work_units'],
            'update_work_units': space.update_meter.stats['work_units'],
            'verification_work_units': sum(verification.values()),
            'extraction_work_units': sum(r['metrics']['work_units'] + r['preparation_work_units']
                                         + r['decode_work_units'] for r in iterations),
            'cache_cells': solver.cache_cells, 'cache_entries': len(solver.cache),
            'general_polynomial_time_bound': False}
