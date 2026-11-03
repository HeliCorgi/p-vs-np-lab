"""A decision-preserving reduction from 3-CNF to binary CNF plus ternary XOR.

For each clause (a OR b OR c), introduce fresh u,v,w, require even parity of
u,v,w, and use (a OR u), (b OR v), (c OR w). The helpers cannot all equal one;
at least one original literal must therefore be true. Conversely a true literal
allows its helper to be zero while the other two are one.

This is an elementary explicit reduction, not a novelty claim. It does not
preserve model counts: a clause with s true literal occurrences AFTER padding
to three occurrences has 2**(s-1) helper extensions. Original variables retain
their positions.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from pnp_lab.affine import AffineRelation


CNF = tuple[tuple[int, ...], ...]


def _holds(cnf: CNF, mask: int) -> bool:
    return all(any(bool((mask >> (abs(literal) - 1)) & 1) == (literal > 0)
                   for literal in clause) for clause in cnf)


@dataclass(frozen=True)
class ThreeSatReduction:
    original_variables: tuple[str, ...]
    original_cnf: CNF
    affine: AffineRelation
    cnf: CNF
    auxiliary_triples: tuple[tuple[int, int, int] | None, ...]

    def lift_witness(self, original_mask: int) -> int:
        """Construct one satisfying extension, rejecting non-model source inputs."""
        if type(original_mask) is not int or not 0 <= original_mask < 1 << len(self.original_variables):
            raise ValueError("Original assignment does not fit the original scope.")
        if not _holds(self.original_cnf, original_mask):
            raise ValueError("Original assignment does not satisfy the source CNF.")
        lifted = original_mask
        for clause, triple in zip(self.original_cnf, self.auxiliary_triples):
            if triple is None:
                raise ValueError("An empty source clause has no satisfying extension.")
            padded = clause + (clause[-1],) * (3 - len(clause))
            selected = next(i for i, literal in enumerate(padded)
                            if bool((original_mask >> (abs(literal) - 1)) & 1) == (literal > 0))
            for i, column in enumerate(triple):
                if i != selected:
                    lifted |= 1 << column
        return lifted

    def project_witness(self, full_mask: int) -> int:
        """Validate a target model, then retain the original variable assignment."""
        if not self.affine.holds_mask(full_mask) or not _holds(self.cnf, full_mask):
            raise ValueError("Assignment does not satisfy the target system.")
        original = full_mask & ((1 << len(self.original_variables)) - 1)
        if not _holds(self.original_cnf, original):
            raise AssertionError("Reduction invariant failed.")
        return original


def three_cnf_to_two_cnf_xor(variables: Sequence[str], clauses: Sequence[Sequence[int]]) -> ThreeSatReduction:
    """Transform every clause of width <=3, using <=3 fresh variables per clause.

    Width-one/two clauses are padded by literal repetition. Empty clauses are
    retained as empty (unsatisfiable) binary-CNF clauses. For exactly-three-
    literal source clauses, all target CNF clauses have width two and all XOR
    equations have arity three; the XOR helper triples are mutually disjoint.
    """
    source_scope = AffineRelation.truth(variables).variables
    source = tuple(tuple(clause) for clause in clauses)
    n = len(source_scope)
    for clause in source:
        if len(clause) > 3:
            raise ValueError("Source clauses must have at most three literals.")
        if any(type(literal) is not int or literal == 0 or abs(literal) > n for literal in clause):
            raise ValueError("Source literals must be nonzero integer indices in the variable scope.")
    names = list(source_scope)
    occupied = set(names)
    equations = []
    binary = []
    triples = []
    for index, clause in enumerate(source):
        if not clause:
            binary.append(())
            triples.append(None)
            continue
        columns = []
        for position in range(3):
            name = f"__pnp_clause_{index}_helper_{position}"
            while name in occupied:
                name += "_"
            occupied.add(name)
            columns.append(len(names))
            names.append(name)
        triple = tuple(columns)
        triples.append(triple)
        equations.append((sum(1 << column for column in columns), 0))
        padded = clause + (clause[-1],) * (3 - len(clause))
        binary.extend((literal, column + 1) for literal, column in zip(padded, columns))
    return ThreeSatReduction(source_scope, source, AffineRelation(tuple(names), tuple(equations)),
                             tuple(binary), tuple(triples))
