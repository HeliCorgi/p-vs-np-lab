"""A decision-preserving 3-CNF bridge with groups of at most five variables.

Pad before copying: every literal occurrence in a padded source clause gets a
fresh variable. Directed implication cycles force copies of the same source
variable to agree. The existing binary-CNF/ternary-XOR bridge then supplies one
helper per expanded literal occurrence. Each copy and all its helpers form one
CNF-local group, containing at most five variables.

This elementary composition preserves satisfiability and constructive witnesses,
not model counts. Bounded local groups do not bound the global signature join.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .affine import AffineRelation
from .reductions import CNF, ThreeSatReduction, three_cnf_to_two_cnf_xor


def _holds(cnf: CNF, assignment: int) -> bool:
    return all(any(bool((assignment >> (abs(literal) - 1)) & 1) == (literal > 0)
                   for literal in clause) for clause in cnf)


@dataclass(frozen=True)
class ConstantBlockReduction:
    """Source metadata, occurrence expansion, target bridge, and local groups.

    ``copy_to_original[i]`` is the zero-based original column represented by
    ``copy_variables[i]``. Groups partition ``bridge.affine.variables`` by name.
    Unused original variables remain in the metadata; projection sets them to
    False because they have no target copies.
    """

    original_variables: tuple[str, ...]
    original_cnf: CNF
    copy_variables: tuple[str, ...]
    copy_to_original: tuple[int, ...]
    expanded_cnf: CNF
    bridge: ThreeSatReduction
    groups: tuple[tuple[str, ...], ...]

    def lift_witness(self, original_mask: int) -> int:
        """Copy a source model's values and construct a satisfying target model."""
        if (type(original_mask) is not int
                or not 0 <= original_mask < 1 << len(self.original_variables)):
            raise ValueError("Original assignment does not fit the original scope.")
        if not _holds(self.original_cnf, original_mask):
            raise ValueError("Original assignment does not satisfy the source CNF.")
        copied = sum(((original_mask >> original) & 1) << copy
                     for copy, original in enumerate(self.copy_to_original))
        return self.bridge.lift_witness(copied)

    def project_witness(self, full_mask: int) -> int:
        """Validate a target model, identify equal copies, and fill unused bits."""
        copied = self.bridge.project_witness(full_mask)
        values: dict[int, int] = {}
        for copy, original in enumerate(self.copy_to_original):
            bit = (copied >> copy) & 1
            if original in values and values[original] != bit:
                raise ValueError("Target assignment gives unequal source-variable copies.")
            values[original] = bit
        projected = sum(bit << original for original, bit in values.items())
        if not _holds(self.original_cnf, projected):
            raise AssertionError("Constant-block reduction invariant failed.")
        return projected


def three_cnf_to_constant_blocks(
    variables: Sequence[str], clauses: Sequence[Sequence[int]],
) -> ConstantBlockReduction:
    """Reduce width-at-most-three CNF to groups of size at most five.

    For a source with m nonempty clauses and no empty clause, the construction
    has exactly 3m groups, at most 4m disjoint ternary XOR rows, and at most 15m
    target variables. Every target CNF clause has width two and lies within one
    group. The signs and repetitions of source literals are retained.

    Validate the complete input before handling empty clauses. Any empty clause
    produces the canonical false target on an empty scope, with no groups. An
    empty source formula produces the canonical true target on an empty scope.
    The original explicit scope is retained even in these special cases.
    """
    original_variables = AffineRelation.truth(variables).variables
    original_cnf = tuple(tuple(clause) for clause in clauses)
    n = len(original_variables)
    for clause in original_cnf:
        if len(clause) > 3:
            raise ValueError("Source clauses must have at most three literals.")
        if any(type(literal) is not int or literal == 0 or abs(literal) > n
               for literal in clause):
            raise ValueError("Source literals must be nonzero integer indices in the variable scope.")
    if any(not clause for clause in original_cnf):
        bridge = three_cnf_to_two_cnf_xor((), ((),))
        return ConstantBlockReduction(original_variables, original_cnf, (), (),
                                      ((),), bridge, ())

    occupied = set(original_variables)
    copy_names: list[str] = []
    copy_to_original: list[int] = []
    copies_by_original: list[list[int]] = [[] for _ in original_variables]
    expanded: list[tuple[int, ...]] = []
    for clause_index, clause in enumerate(original_cnf):
        padded = clause + (clause[-1],) * (3 - len(clause))
        copied_clause = []
        for position, literal in enumerate(padded):
            name = f"__pnp_occurrence_{clause_index}_{position}"
            while name in occupied:
                name += "_"
            occupied.add(name)
            copy_names.append(name)
            original = abs(literal) - 1
            copy_to_original.append(original)
            copy_index = len(copy_names)  # DIMACS indices are one-based.
            copies_by_original[original].append(copy_index)
            copied_clause.append(copy_index if literal > 0 else -copy_index)
        expanded.append(tuple(copied_clause))

    for copies in copies_by_original:
        if len(copies) >= 2:
            for index, current in enumerate(copies):
                following = copies[(index + 1) % len(copies)]
                expanded.append((-current, following, following))

    copy_variables = tuple(copy_names)
    expanded_cnf = tuple(expanded)
    bridge = three_cnf_to_two_cnf_xor(copy_variables, expanded_cnf)
    group_names = [[name] for name in copy_variables]
    for clause, triple in zip(expanded_cnf, bridge.auxiliary_triples):
        if triple is None:
            raise AssertionError("The occurrence expansion contains an empty clause.")
        for literal, helper in zip(clause, triple):
            group_names[abs(literal) - 1].append(bridge.affine.variables[helper])
    groups = tuple(tuple(group) for group in group_names)
    return ConstantBlockReduction(original_variables, original_cnf, copy_variables,
                                  tuple(copy_to_original), expanded_cnf, bridge, groups)
