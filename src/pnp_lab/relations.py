"""Exact finite color relations and existential composition.

Rows always retain their *labeled* colors. Natural joins match shared variables
using those labels; independently canonicalizing the inputs would be unsound.
Canonical color partitions are an optional summary of a relation verified to
be invariant under every permutation of the palette. Named-color restrictions
are supported by ordinary rows, but are not assumed to have this symmetry.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product
from typing import Callable, Iterable, Iterator, Mapping, Sequence


ColorRow = tuple[int, ...]


def canonicalize_colors(colors: Iterable[int]) -> ColorRow:
    """Rename colors by first occurrence without reordering the positions."""
    names: dict[int, int] = {}
    result = []
    for color in colors:
        if color not in names:
            names[color] = len(names)
        result.append(names[color])
    return tuple(result)


def canonical_partitions(length: int, max_colors: int) -> Iterator[ColorRow]:
    """Enumerate restricted-growth strings in lexicographic order."""
    if type(length) is not int or length < 0:
        raise ValueError("length must be a nonnegative integer")
    if type(max_colors) is not int or max_colors < 1:
        raise ValueError("max_colors must be a positive integer")
    if length == 0:
        yield ()
        return
    row = [0] * length

    def visit(position: int, largest: int) -> Iterator[ColorRow]:
        if position == length:
            yield tuple(row)
            return
        for color in range(min(largest + 1, max_colors - 1) + 1):
            row[position] = color
            yield from visit(position + 1, max(largest, color))

    yield from visit(1, 0)


def _variables(values: Sequence[str]) -> tuple[str, ...]:
    result = tuple(values)
    if any(not isinstance(value, str) or not value for value in result):
        raise ValueError("variable names must be nonempty strings")
    if len(set(result)) != len(result):
        raise ValueError("variable names must be distinct")
    return result


def _color_count(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("color_count must be a positive integer")
    return value


@dataclass(frozen=True)
class FiniteRelation:
    """A set of labeled rows on an ordered tuple of variables.

    ``join`` / ``conjoin`` form conjunction on the union of variable scopes.
    ``project`` existentially eliminates all variables not retained. These are
    exact finite operations; their explicit tables can grow exponentially.
    """

    variables: tuple[str, ...]
    color_count: int
    rows: frozenset[ColorRow]

    def __post_init__(self) -> None:
        variables = _variables(self.variables)
        color_count = _color_count(self.color_count)
        rows = frozenset(tuple(row) for row in self.rows)
        for row in rows:
            if len(row) != len(variables):
                raise ValueError("row length must match the variable scope")
            if any(type(color) is not int or not 0 <= color < color_count for color in row):
                raise ValueError("row colors must be integers in range(color_count)")
        object.__setattr__(self, "variables", variables)
        object.__setattr__(self, "color_count", color_count)
        object.__setattr__(self, "rows", rows)

    @classmethod
    def from_predicate(
        cls,
        variables: Sequence[str],
        color_count: int,
        predicate: Callable[[Mapping[str, int]], bool],
    ) -> FiniteRelation:
        scope = _variables(variables)
        _color_count(color_count)
        return cls(scope, color_count, frozenset(
            row for row in product(range(color_count), repeat=len(scope))
            if predicate(dict(zip(scope, row)))
        ))

    @classmethod
    def truth(cls, color_count: int) -> FiniteRelation:
        """The true relation on the empty scope; identity for conjunction."""
        return cls((), color_count, frozenset({()}))

    @classmethod
    def equality(cls, left: str, right: str, color_count: int) -> FiniteRelation:
        scope = (left,) if left == right else (left, right)
        return cls.from_predicate(scope, color_count, lambda row: row[left] == row[right])

    @classmethod
    def disequality(cls, left: str, right: str, color_count: int) -> FiniteRelation:
        scope = (left,) if left == right else (left, right)
        return cls.from_predicate(scope, color_count, lambda row: row[left] != row[right])

    def join(self, other: FiniteRelation) -> FiniteRelation:
        """Natural join on shared variable names and their actual color labels.

        Output order is this scope followed by new variables from the other
        scope. No assumptions about color-renaming symmetry are required.
        """
        if self.color_count != other.color_count:
            raise ValueError("joined relations must use the same palette")
        left_positions = {name: i for i, name in enumerate(self.variables)}
        right_positions = {name: i for i, name in enumerate(other.variables)}
        shared = tuple(name for name in self.variables if name in right_positions)
        left_shared = tuple(left_positions[name] for name in shared)
        right_shared = tuple(right_positions[name] for name in shared)
        new_right = tuple(i for i, name in enumerate(other.variables) if name not in left_positions)
        scope = self.variables + tuple(other.variables[i] for i in new_right)
        if not self.rows or not other.rows:
            return FiniteRelation(scope, self.color_count, frozenset())
        indexed: dict[ColorRow, list[ColorRow]] = defaultdict(list)
        for row in other.rows:
            indexed[tuple(row[i] for i in right_shared)].append(row)
        joined = set()
        for left_row in self.rows:
            match = tuple(left_row[i] for i in left_shared)
            for right_row in indexed.get(match, ()):
                joined.add(left_row + tuple(right_row[i] for i in new_right))
        return FiniteRelation(scope, self.color_count, frozenset(joined))

    def conjoin(self, other: FiniteRelation) -> FiniteRelation:
        """Conjunction of scoped predicates, implemented by natural join."""
        return self.join(other)

    def project(self, variables: Sequence[str]) -> FiniteRelation:
        """Existentially eliminate the complement, preserving the given order."""
        scope = _variables(variables)
        positions = {name: i for i, name in enumerate(self.variables)}
        unknown = set(scope) - set(positions)
        if unknown:
            raise ValueError(f"unknown projection variables: {sorted(unknown)}")
        selected = tuple(positions[name] for name in scope)
        return FiniteRelation(scope, self.color_count, frozenset(
            tuple(row[i] for i in selected) for row in self.rows
        ))

    def exists(self, variables: Sequence[str]) -> FiniteRelation:
        """Eliminate the named variables and retain the original order."""
        eliminated = set(_variables(variables))
        unknown = eliminated - set(self.variables)
        if unknown:
            raise ValueError(f"unknown existential variables: {sorted(unknown)}")
        return self.project(tuple(name for name in self.variables if name not in eliminated))

    def is_color_symmetric(self) -> bool:
        """Check that every represented palette-permutation orbit is complete."""
        orbit_counts = Counter(canonicalize_colors(row) for row in self.rows)
        for canonical, observed in orbit_counts.items():
            expected = 1
            for offset in range(len(set(canonical))):
                expected *= self.color_count - offset
            if observed != expected:
                return False
        return True

    def canonical_rows(self) -> tuple[ColorRow, ...]:
        """Summarize a verified color-symmetric relation by ordered partitions.

        Named-color pinnings usually break this symmetry and raise ValueError.
        The original labeled rows are never changed by this operation.
        """
        if not self.is_color_symmetric():
            raise ValueError("canonical summary requires full color-renaming symmetry")
        return tuple(sorted({canonicalize_colors(row) for row in self.rows}))


def conjoin_all(relations: Iterable[FiniteRelation], color_count: int) -> FiniteRelation:
    result = FiniteRelation.truth(color_count)
    for relation in relations:
        result = result.join(relation)
    return result


@dataclass(frozen=True)
class ColorLiteral:
    """A predicate c(left)=c(right) or c(left)!=c(right), not a free Boolean."""

    left: str
    right: str
    equal: bool = True

    def __post_init__(self) -> None:
        if any(not isinstance(name, str) or not name for name in (self.left, self.right)):
            raise ValueError("literal variable names must be nonempty strings")
        if type(self.equal) is not bool:
            raise ValueError("equal must be a Boolean")

    def evaluate(self, assignment: Mapping[str, int]) -> bool:
        same = assignment[self.left] == assignment[self.right]
        return same if self.equal else not same

    def as_dict(self) -> dict:
        return {"left": self.left, "right": self.right, "kind": "eq" if self.equal else "neq"}


def clause_holds(literals: Iterable[ColorLiteral], assignment: Mapping[str, int]) -> bool:
    """Disjunction, including the convention that the empty clause is false."""
    return any(literal.evaluate(assignment) for literal in literals)


def cnf_holds(clauses: Iterable[Iterable[ColorLiteral]], assignment: Mapping[str, int]) -> bool:
    """Conjunction of clauses, with the empty conjunction true."""
    return all(clause_holds(clause, assignment) for clause in clauses)
