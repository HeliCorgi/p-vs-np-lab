"""Auditable finite-size SAT experiments, not an asymptotic complexity test.

The DPLL engines deliberately omit learning/restarts and are not competitive
with modern SAT solvers. Literal inspections are a deterministic work proxy.
Certificates are checked by separate routines on the original formula.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import math
import random


def validate(n, clauses):
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer")
    for clause in clauses:
        if any(type(lit) is not int or not 1 <= abs(lit) <= n for lit in clause):
            raise ValueError("invalid literal")
        if len({abs(lit) for lit in clause}) != len(clause):
            raise ValueError("use clauses without repeated variables")


def satisfies(clauses, word):
    return all(any(bool(word & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in clause) for clause in clauses)


def brute_force(n, clauses):
    return next((word for word in range(1 << n) if satisfies(clauses, word)), None)


class WorkLimit(Exception):
    pass


def dpll(n, clauses, heuristic="shortest", budget=2_000_000):
    """Complete unbudgeted DPLL; a budget interruption is explicitly UNKNOWN.

    'first' uses the lowest unassigned index and positive polarity. 'shortest'
    counts occurrences in shortest residual clauses, then chooses the most
    frequent variable/polarity, breaking ties by index/positive polarity.
    """
    clauses = tuple(tuple(c) for c in clauses)
    validate(n, clauses)
    if heuristic not in ("first", "shortest"):
        raise ValueError("unknown heuristic")
    if budget is not None and (type(budget) is not int or budget < 0):
        raise ValueError("invalid budget")
    stats = dict(literal_inspections=0, nodes=0, decisions=0, propagations=0)

    def tick():
        if budget is not None and stats["literal_inspections"] >= budget:
            raise WorkLimit
        stats["literal_inspections"] += 1

    def search(active, assignment):
        stats["nodes"] += 1
        units = []
        while True:
            reduced = []
            unit = None
            for index, clause in active:
                rest = []
                satisfied = False
                for lit in clause:
                    tick()
                    value = assignment.get(abs(lit))
                    if value is None:
                        rest.append(lit)
                    elif value == (lit > 0):
                        satisfied = True
                        break
                if satisfied:
                    continue
                if not rest:
                    return None, dict(units=units, conflict=index)
                reduced.append((index, tuple(rest)))
                if len(rest) == 1 and unit is None:
                    unit = (rest[0], index)
            if not reduced:
                word = sum(1 << (v - 1) for v, value in assignment.items() if value)
                return word, None
            active = reduced
            if unit is None:
                break
            lit, index = unit
            units.append((lit, index))
            stats["propagations"] += 1
            assignment[abs(lit)] = lit > 0
        counts = Counter()
        shortest = min(len(c) for _, c in active)
        for _, clause in active:
            for lit in clause:
                tick()
                if heuristic == "first" or len(clause) == shortest:
                    counts[lit] += 1
        variables = {abs(lit) for lit in counts}
        if heuristic == "first":
            variable = min(variables)
            positive = True
        else:
            variable = min(variables, key=lambda v: (-(counts[v] + counts[-v]), v))
            positive = counts[variable] >= counts[-variable]
        stats["decisions"] += 1
        children = {}
        for value in (positive, not positive):
            child_assignment = dict(assignment)
            child_assignment[variable] = value
            word, proof = search(active, child_assignment)
            if word is not None:
                return word, None
            children[str(int(value))] = proof
        return None, dict(units=units, variable=variable, children=children)

    try:
        word, proof = search(list(enumerate(clauses)), {})
        status = "SAT" if word is not None else "UNSAT"
    except WorkLimit:
        word = proof = None
        status = "UNKNOWN"
    return dict(status=status, witness=word, proof=proof, **stats)


def check_refutation(n, clauses, proof):
    """Replay unit reasons and both branches without invoking a SAT solver."""
    def visit(node, assignment):
        for lit, index in node["units"]:
            if not 0 <= index < len(clauses) or abs(lit) in assignment:
                return False
            unassigned = []
            for other in clauses[index]:
                if abs(other) not in assignment:
                    unassigned.append(other)
                elif assignment[abs(other)] == (other > 0):
                    return False
            if unassigned != [lit]:
                return False
            assignment[abs(lit)] = lit > 0
        if "conflict" in node:
            index = node["conflict"]
            return (0 <= index < len(clauses) and
                    all(abs(lit) in assignment and assignment[abs(lit)] != (lit > 0)
                        for lit in clauses[index]))
        variable = node["variable"]
        if type(variable) is not int or not 1 <= variable <= n or variable in assignment:
            return False
        return all(visit(node["children"][str(value)], {**assignment, variable: bool(value)})
                   for value in (0, 1))
    try:
        validate(n, clauses)
        return visit(proof, {})
    except (KeyError, TypeError, ValueError, IndexError):
        return False


def xor_clauses(variables, rhs):
    """Forbid exactly the words with wrong XOR parity (used for width 3)."""
    return [tuple(-v if bit else v for v, bit in zip(variables, word))
            for word in product((0, 1), repeat=len(variables)) if sum(word) % 2 != rhs]


def recognize_xor(n, clauses):
    """Read complete width-3 parity blocks from CNF; no generator metadata."""
    validate(n, clauses)
    groups = {}
    for clause in clauses:
        if len(clause) != 3:
            return None
        scope = tuple(sorted(abs(lit) for lit in clause))
        negative = frozenset(abs(lit) for lit in clause if lit < 0)
        groups.setdefault(scope, set()).add(negative)
    equations = []
    for scope, patterns in sorted(groups.items()):
        parities = {len(p) % 2 for p in patterns}
        if len(patterns) != 4 or len(parities) != 1:
            return None
        equations.append((sum(1 << (v - 1) for v in scope), 1 - parities.pop()))
    return equations


def gaussian(n, equations):
    """Solve GF(2) equations, retaining a checkable inconsistent row sum."""
    pivots = {}
    row_xors = 0
    for index, (mask, rhs) in enumerate(equations):
        if type(mask) is not int or not 0 <= mask < (1 << n) or rhs not in (0, 1):
            raise ValueError("invalid GF(2) row")
        origin = 1 << index
        while mask:
            pivot = (mask & -mask).bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (mask, rhs, origin)
                break
            other, bit, provenance = pivots[pivot]
            mask ^= other
            rhs ^= bit
            origin ^= provenance
            row_xors += 1
        if not mask and rhs:
            return dict(status="UNSAT", witness=None, contradiction=origin,
                        rank=len(pivots), row_xors=row_xors)
    word = 0
    for pivot, (mask, rhs, _) in sorted(pivots.items(), reverse=True):
        if (mask & word).bit_count() % 2 != rhs:
            word |= 1 << pivot
    return dict(status="SAT", witness=word, contradiction=None,
                rank=len(pivots), row_xors=row_xors)


def check_row_contradiction(equations, selector):
    if type(selector) is not int or not 0 < selector < (1 << len(equations)):
        return False
    mask = rhs = 0
    for index, (row, bit) in enumerate(equations):
        if selector & (1 << index):
            mask ^= row
            rhs ^= bit
    return mask == 0 and rhs == 1


def random_three_cnf(n, density_numerator, density_denominator, seed):
    rng = random.Random(seed)
    count = n * density_numerator // density_denominator
    if n < 3 or count > 8 * math.comb(n, 3):
        raise ValueError("invalid random formula parameters")
    seen = set()
    clauses = []
    while len(clauses) < count:
        scope = sorted(rng.sample(range(1, n + 1), 3))
        clause = tuple(v if rng.getrandbits(1) else -v for v in scope)
        if clause not in seen:
            seen.add(clause)
            clauses.append(clause)
    return tuple(clauses)


def graph_xor_cnf(n, odd, seed):
    """Cycle plus a random disjoint perfect matching; n labels the edges."""
    if n < 12 or n % 3:
        raise ValueError("n must be a multiple of three, at least twelve")
    rng = random.Random(seed)
    vertices = 2 * n // 3
    cycle = {(i, i + 1) for i in range(vertices - 1)} | {(0, vertices - 1)}
    order = list(range(vertices))
    while True:
        rng.shuffle(order)
        matching = {tuple(sorted(order[i:i + 2])) for i in range(0, vertices, 2)}
        if not cycle.intersection(matching):
            break
    edges = sorted(cycle | matching)
    rng.shuffle(edges)
    charges = [rng.getrandbits(1) for _ in range(vertices - 1)]
    charges.append((sum(charges) + int(odd)) % 2)
    clauses = []
    for v, charge in enumerate(charges):
        scope = [i + 1 for i, edge in enumerate(edges) if v in edge]
        assert len(scope) == 3
        clauses.extend(xor_clauses(scope, charge))
    rng.shuffle(clauses)
    return tuple(clauses)


MODEL_FEATURES = {
    "polynomial": math.log2,
    "exponential": float,
    "sqrt_exponential": math.sqrt,
}


def fit_growth(sizes, costs, train_count):
    """Fit log2(cost+1) on smaller sizes; evaluate only on held-out sizes."""
    if not 2 <= train_count < len(sizes) or len(costs) != len(sizes):
        raise ValueError("need training and held-out observations")
    if any(n <= 0 for n in sizes) or any(c < 0 for c in costs):
        raise ValueError("invalid observations")
    ys = [math.log2(c + 1) for c in costs]
    fits = {}
    for name, feature in MODEL_FEATURES.items():
        xs = [feature(n) for n in sizes]
        xbar = sum(xs[:train_count]) / train_count
        ybar = sum(ys[:train_count]) / train_count
        variance = sum((x - xbar) ** 2 for x in xs[:train_count])
        slope = sum((x - xbar) * (y - ybar)
                    for x, y in zip(xs[:train_count], ys[:train_count])) / variance
        intercept = ybar - slope * xbar
        errors = [y - (intercept + slope * x)
                  for x, y in zip(xs[train_count:], ys[train_count:])]
        fits[name] = dict(slope=round(slope, 8), intercept=round(intercept, 8),
                          held_out_log2_rmse=round(math.sqrt(sum(e * e for e in errors) / len(errors)), 8))
    return fits
