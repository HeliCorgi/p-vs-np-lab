"""Small certificates that a CNF model set has full affine hull over GF(2).

A certificate gives a CNF model and, for every coordinate j, two CNF models
whose XOR is the unit vector e_j. Any affine equation valid on every model has
zero coefficient at j. The base model also forces its constant term to zero,
including when there are no variables. This is not a general affine-hull solver.

The constructor covers clauses (signed original literal OR positive helper),
where each helper occurs at most once. It applies to the CNF part of the lab's
3SAT bridge. It deliberately does not include that bridge's XOR constraints.
"""

from __future__ import annotations

from typing import Iterable


def _validated_cnf(n_variables: int, cnf: Iterable[Iterable[int]]) -> tuple[tuple[int, ...], ...]:
    if type(n_variables) is not int or n_variables < 0:
        raise ValueError("n_variables must be a nonnegative integer.")
    clauses = tuple(tuple(clause) for clause in cnf)
    for clause in clauses:
        if any(type(lit) is not int or lit == 0 or abs(lit) > n_variables for lit in clause):
            raise ValueError("CNF literals must be nonzero integers within the variable scope.")
    return clauses


def _holds(clauses: tuple[tuple[int, ...], ...], assignment: int) -> bool:
    return all(any(((assignment >> (abs(lit) - 1)) & 1) == int(lit > 0)
                   for lit in clause) for clause in clauses)


def coordinate_separation_certificate_for_leaf_cnf(
    n_variables: int,
    original_variables: int,
    cnf: Iterable[Iterable[int]],
) -> dict:
    """Construct a full-hull witness for the explicitly stated leaf-clause form.

Variables 1..original_variables are original; the remaining ones are helpers.
Every clause must contain one original literal and one positive helper. A
helper can be unused but cannot occur in two clauses, even duplicate clauses.
    The returned O(n_variables**2)-bit witness can be checked against raw CNF alone.
    Polynomial input-size claims require an explicit variable scope (as in the
    bridge API), rather than charging only the binary length of n_variables.
"""
    clauses = _validated_cnf(n_variables, cnf)
    if (type(original_variables) is not int
            or not 0 <= original_variables <= n_variables):
        raise ValueError("original_variables must be an integer within the scope.")
    helper_sources: dict[int, int] = {}
    for clause in clauses:
        if len(clause) != 2:
            raise ValueError("Each leaf clause must have exactly two literals.")
        originals = [lit for lit in clause if abs(lit) <= original_variables]
        helpers = [lit for lit in clause if lit > original_variables]
        if len(originals) != 1 or len(helpers) != 1:
            raise ValueError("Expected one original literal and one positive helper.")
        helper = helpers[0] - 1
        if helper in helper_sources:
            raise ValueError("Each helper may occur in at most one clause.")
        helper_sources[helper] = originals[0]

    helpers_true = ((1 << n_variables) - 1) ^ ((1 << original_variables) - 1)
    pairs = []
    for coordinate in range(n_variables):
        left = helpers_true
        if coordinate >= original_variables:
            literal = helper_sources.get(coordinate)
            if literal is not None and literal > 0:
                left |= 1 << (literal - 1)
        pairs.append({"coordinate": coordinate, "left": left,
                      "right": left ^ (1 << coordinate)})
    return {"kind": "cnf-coordinate-separation-v1", "n_variables": n_variables,
            "base_model": helpers_true, "pairs": pairs}


def check_cnf_coordinate_separation(
    n_variables: int,
    cnf: Iterable[Iterable[int]],
    certificate: object,
) -> bool:
    """Independently check membership and each unit difference; no solver used.

This checker does not need the leaf-clause restriction or the original/helper
partition. Success certifies only the affine hull of this CNF's model set.
It does not claim that the CNF is a tautology, or solve a CNF+XOR conjunction.
"""
    try:
        clauses = _validated_cnf(n_variables, cnf)
        if (not isinstance(certificate, dict)
                or set(certificate) != {"kind", "n_variables", "base_model", "pairs"}
                or certificate["kind"] != "cnf-coordinate-separation-v1"
                or type(certificate["n_variables"]) is not int
                or certificate["n_variables"] != n_variables):
            return False
        limit = 1 << n_variables

        def valid_model(assignment: object) -> bool:
            return (type(assignment) is int and 0 <= assignment < limit
                    and _holds(clauses, assignment))

        if not valid_model(certificate["base_model"]):
            return False
        pairs = certificate["pairs"]
        if not isinstance(pairs, list) or len(pairs) != n_variables:
            return False
        for coordinate, pair in enumerate(pairs):
            if (not isinstance(pair, dict) or set(pair) != {"coordinate", "left", "right"}
                    or type(pair["coordinate"]) is not int
                    or pair["coordinate"] != coordinate):
                return False
            left, right = pair["left"], pair["right"]
            if (not valid_model(left) or not valid_model(right)
                    or left ^ right != 1 << coordinate):
                return False
        return True
    except (TypeError, ValueError, KeyError, OverflowError):
        return False
