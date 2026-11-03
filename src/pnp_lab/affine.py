"""Exact affine Boolean relations, closed under join and existential projection.

An equation is (mask, rhs).  Bit i of mask selects variables[i]; selected bits
sum to rhs modulo two.  There is no OR/CNF interpretation.  Python integers
store finite coefficient rows; operations on long integers are not unit cost.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Mapping, Sequence


Equation = tuple[int, int]


def _scope(variables: Sequence[str]) -> tuple[str, ...]:
    result = tuple(variables)
    if any(not isinstance(name, str) or not name for name in result):
        raise ValueError("Variable names must be nonempty strings.")
    if len(set(result)) != len(result):
        raise ValueError("Variable names must be distinct.")
    return result


def _rref(equations: Iterable[Equation], n: int,
          pivot_order: Sequence[int] | None = None) -> tuple[Equation, ...]:
    """Exact reduced row echelon form; a contradiction is canonical (0, 1)."""
    coefficients = (1 << n) - 1
    rows = [mask | (rhs << n) for mask, rhs in equations]
    order = tuple(range(n)) if pivot_order is None else tuple(pivot_order)
    if len(order) != n or set(order) != set(range(n)):
        raise ValueError("Pivot order must be a permutation of all columns.")
    rank = 0
    for column in order:
        pivot = next((index for index in range(rank, len(rows))
                      if (rows[index] >> column) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_row = rows[rank]
        for index in range(len(rows)):
            if index != rank and (rows[index] >> column) & 1:
                rows[index] ^= pivot_row
        rank += 1
    if any((row & coefficients) == 0 and (row >> n) == 1 for row in rows):
        return ((0, 1),)
    return tuple((row & coefficients, row >> n) for row in rows if row & coefficients)


def _remap(mask: int, positions: Sequence[int]) -> int:
    result = 0
    while mask:
        lowest = mask & -mask
        result |= 1 << positions[lowest.bit_length() - 1]
        mask ^= lowest
    return result


@dataclass(frozen=True)
class AffineRelation:
    """An exact solution set of a finite GF(2) linear system.

    Rows are reduced on construction.  () means no constraints; ((0, 1),)
    means false on any scope, including the empty scope.  Output scopes of
    project/reorder preserve the order explicitly requested by the caller.
    """

    variables: tuple[str, ...]
    equations: tuple[Equation, ...]

    def __post_init__(self) -> None:
        variables = _scope(self.variables)
        rows = []
        for equation in self.equations:
            if len(equation) != 2:
                raise ValueError("Each equation must be a (mask, rhs) pair.")
            mask, rhs = equation
            if type(mask) is not int or not 0 <= mask < 1 << len(variables):
                raise ValueError("Equation mask must fit the variable scope.")
            if type(rhs) is not int or rhs not in (0, 1):
                raise ValueError("Equation right-hand sides must be integer 0 or 1.")
            rows.append((mask, rhs))
        object.__setattr__(self, "variables", variables)
        object.__setattr__(self, "equations", _rref(rows, len(variables)))

    @classmethod
    def from_named(cls, variables: Sequence[str],
                   equations: Iterable[tuple[Iterable[str], int]]) -> AffineRelation:
        """Build equations from (variable-name terms, rhs); repeated names cancel."""
        scope = _scope(variables)
        positions = {name: index for index, name in enumerate(scope)}
        rows = []
        for terms, rhs in equations:
            if isinstance(terms, str):
                raise ValueError("Pass an iterable of variable names, not one string.")
            mask = 0
            for name in terms:
                if name not in positions:
                    raise ValueError(f"Unknown equation variable: {name!r}")
                mask ^= 1 << positions[name]
            rows.append((mask, rhs))
        return cls(scope, tuple(rows))

    @classmethod
    def truth(cls, variables: Sequence[str] = ()) -> AffineRelation:
        return cls(tuple(variables), ())

    @classmethod
    def false(cls, variables: Sequence[str] = ()) -> AffineRelation:
        return cls(tuple(variables), ((0, 1),))

    @property
    def is_consistent(self) -> bool:
        return self.equations != ((0, 1),)

    def holds_mask(self, assignment: int) -> bool:
        """Evaluate a complete assignment in this relation's variable order."""
        if type(assignment) is not int or not 0 <= assignment < 1 << len(self.variables):
            raise ValueError("Assignment must be a nonnegative mask fitting the scope.")
        return all((mask & assignment).bit_count() % 2 == rhs for mask, rhs in self.equations)

    def holds(self, assignment: Mapping[str, int]) -> bool:
        """Evaluate named bits; extra names are allowed, missing scoped names are not."""
        mask = 0
        for index, name in enumerate(self.variables):
            if name not in assignment:
                raise ValueError(f"Missing assignment for {name!r}")
            bit = assignment[name]
            if type(bit) is not int or bit not in (0, 1):
                raise ValueError("Assignment values must be integer 0 or 1.")
            mask |= bit << index
        return self.holds_mask(mask)

    def join(self, other: AffineRelation) -> AffineRelation:
        """Conjoin equations; shared names refer to the same Boolean variable."""
        scope = self.variables + tuple(name for name in other.variables if name not in self.variables)
        target = {name: index for index, name in enumerate(scope)}
        rows = []
        for relation in (self, other):
            positions = tuple(target[name] for name in relation.variables)
            rows.extend((_remap(mask, positions), rhs) for mask, rhs in relation.equations)
        return AffineRelation(scope, tuple(rows))

    def conjoin(self, other: AffineRelation) -> AffineRelation:
        return self.join(other)

    def project(self, variables: Sequence[str]) -> AffineRelation:
        """Existentially hide the complement using hidden-column-first elimination.

        Each hidden pivot equation can solve its pivot variable for every
        retained assignment satisfying the remaining rows.  Dropping those
        pivot rows is therefore existential elimination, not just deletion of
        the original equations that mention hidden variables.
        """
        retained = _scope(variables)
        old = {name: index for index, name in enumerate(self.variables)}
        unknown = set(retained) - set(old)
        if unknown:
            raise ValueError(f"Unknown projection variables: {sorted(unknown)}")
        kept_columns = tuple(old[name] for name in retained)
        hidden = tuple(index for index, name in enumerate(self.variables) if name not in retained)
        hidden_mask = sum(1 << index for index in hidden)
        reduced = _rref(self.equations, len(self.variables), hidden + kept_columns)
        positions = {column: index for index, column in enumerate(kept_columns)}
        projected = []
        for mask, rhs in reduced:
            if mask & hidden_mask:
                continue
            new_mask = sum(1 << positions[column] for column in kept_columns if (mask >> column) & 1)
            projected.append((new_mask, rhs))
        return AffineRelation(retained, tuple(projected))

    def exists(self, variables: Sequence[str]) -> AffineRelation:
        eliminated = _scope(variables)
        unknown = set(eliminated) - set(self.variables)
        if unknown:
            raise ValueError(f"Unknown existential variables: {sorted(unknown)}")
        return self.project(tuple(name for name in self.variables if name not in eliminated))

    def reorder(self, variables: Sequence[str]) -> AffineRelation:
        reordered = _scope(variables)
        if set(reordered) != set(self.variables):
            raise ValueError("Reorder must preserve exactly the original variable set.")
        return self.project(reordered)
