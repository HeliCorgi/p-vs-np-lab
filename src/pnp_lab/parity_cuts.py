"""Certified, polynomial exactly-one parity strengthening for XOR + CNF.

A cover clause (l_1 OR ... OR l_s), together with every binary exclusion
(NOT l_i OR NOT l_j), entails XOR_i value(l_i) = 1.  The empty cover is
already false and entails 0 = 1; a unit cover gives a unit XOR.  We inspect
only literal sets already present as clauses, never arbitrary cliques.

All cuts are consequences of the original CNF, which is retained unchanged.
They preserve the complete set of models, not merely satisfiability.  Finding
these cuts and checking their certificates take polynomial bit time.  The
fallback quotient enumeration remains potentially exponential.

The trusted input XOR rows are AffineRelation.equations, already normalized
by that class.  A linear contradiction certificate cites a combination of
those rows and checked cuts; its checker performs row XOR only, without
Gaussian elimination.  This is not a proof of normalization from raw XOR
input, nor a formal verification of the Python implementation.
"""

from __future__ import annotations

from collections.abc import Iterable
from itertools import combinations
from typing import Any

from .affine import AffineRelation, Equation
from .mixed import (
    CNF,
    _normalize_cnf,
    _problem,
    check_sat_witness,
    check_unsat_certificate,
    solve_mixed,
)


def _linear_contradiction(rows: list[Equation]) -> dict[str, Any] | None:
    """Echelon elimination with a bit vector recording source-row sums."""
    pivots: dict[int, tuple[int, int, int]] = {}
    for index, (source_mask, source_rhs) in enumerate(rows):
        mask, rhs, provenance = source_mask, source_rhs, 1 << index
        while mask:
            column = mask.bit_length() - 1
            if column not in pivots:
                pivots[column] = mask, rhs, provenance
                break
            other_mask, other_rhs, other_provenance = pivots[column]
            mask ^= other_mask
            rhs ^= other_rhs
            provenance ^= other_provenance
        if not mask and rhs:
            return {
                "combination": [i for i in range(len(rows)) if (provenance >> i) & 1],
                "equation": [0, 1],
            }
    return None


def derive_parity_cuts(
    affine: AffineRelation, cnf: Iterable[Iterable[int]],
) -> dict[str, Any]:
    """Find all covers supported by explicit binary exclusions in one pass.

    Clause references are zero-based indices in the ORIGINAL CNF.  Each
    distinct normalized, non-tautological clause is considered once.  For a
    cover sorted by (abs(literal), literal), exclusion references are listed
    in the order of itertools.combinations(cover, 2).  Row references in a
    contradiction address input affine rows first, then cuts in list order.

    A missing contradiction is not an UNSAT certificate or a claim that the
    complete mixed formula is satisfiable.  Certificates can be checked with
    check_parity_cut_certificate independently of this finder/eliminator.
    """
    raw_cnf = _problem(affine, cnf)
    normalized = _normalize_cnf(raw_cnf)
    first_source: dict[frozenset[int], int] = {}
    for index, clause in enumerate(raw_cnf):
        literals = frozenset(clause)
        if not any(-literal in literals for literal in literals):
            first_source.setdefault(literals, index)
    binary_sources = {clause: index for clause, index in first_source.items() if len(clause) == 2}
    cuts = []
    for cover in normalized:
        exclusions = []
        for left, right in combinations(cover, 2):
            source = binary_sources.get(frozenset((-left, -right)))
            if source is None:
                break
            exclusions.append(source)
        else:
            # No opposite literals or repeats remain in a normalized cover.
            mask = sum(1 << (abs(literal) - 1) for literal in cover)
            rhs = 1 ^ (sum(literal < 0 for literal in cover) & 1)
            cuts.append({
                "cover_clause": first_source[frozenset(cover)],
                "exclusion_clauses": exclusions,
                "equation": [mask, rhs],
            })
    rows = list(affine.equations) + [tuple(cut["equation"]) for cut in cuts]
    return {
        "kind": "exactly-one-parity-cuts-v1",
        "n_variables": len(affine.variables),
        "input_clause_count": len(raw_cnf),
        "input_affine_row_count": len(affine.equations),
        "cuts": cuts,
        "contradiction": _linear_contradiction(rows),
    }


def _referenced_clause(raw_cnf: CNF, index: Any) -> tuple[int, ...] | None:
    """Checker-side duplicate removal; does not call the finder's normalizer."""
    if type(index) is not int or not 0 <= index < len(raw_cnf):
        return None
    literals = []
    for literal in raw_cnf[index]:
        if -literal in literals:
            return None
        if literal not in literals:
            literals.append(literal)
    return tuple(sorted(literals, key=lambda literal: (abs(literal), literal)))


def _equation(value: Any, n: int) -> bool:
    return (isinstance(value, list) and len(value) == 2
            and type(value[0]) is int and 0 <= value[0] < 1 << n
            and type(value[1]) is int and value[1] in (0, 1))


def check_parity_cut_certificate(
    affine: AffineRelation, cnf: Iterable[Iterable[int]], certificate: Any,
) -> bool:
    """Check sound cut inferences and any claimed linear contradiction.

    This checks cited premises directly, not by rerunning the finder or its
    Gaussian elimination.  It deliberately need not establish that every
    possible cut was found.  With contradiction=None it certifies only that
    adding these cuts preserves the original models, NOT that the input is
    SAT or UNSAT.  Invalid problem input raises ValueError; an invalid proof
    of a valid problem returns False.
    """
    raw_cnf = _problem(affine, cnf)
    if not isinstance(certificate, dict) or certificate.get("kind") != "exactly-one-parity-cuts-v1":
        return False
    n = len(affine.variables)
    for field, expected in (("n_variables", n), ("input_clause_count", len(raw_cnf)),
                            ("input_affine_row_count", len(affine.equations))):
        if type(certificate.get(field)) is not int or certificate[field] != expected:
            return False
    cuts = certificate.get("cuts")
    if not isinstance(cuts, list) or len(cuts) > len(raw_cnf) or "contradiction" not in certificate:
        return False
    checked_covers = set()
    rows = list(affine.equations)
    for cut in cuts:
        if not isinstance(cut, dict):
            return False
        cover = _referenced_clause(raw_cnf, cut.get("cover_clause"))
        if cover is None or cover in checked_covers:
            return False
        checked_covers.add(cover)
        exclusions = cut.get("exclusion_clauses")
        width = len(cover)
        if not isinstance(exclusions, list) or len(exclusions) != width * (width - 1) // 2:
            return False
        if any(type(index) is not int for index in exclusions):
            return False
        if len(set(exclusions)) != len(exclusions):
            return False
        offset = 0
        for left in range(width):
            for right in range(left + 1, width):
                clause = _referenced_clause(raw_cnf, exclusions[offset])
                if (clause is None or len(clause) != 2
                        or -cover[left] not in clause or -cover[right] not in clause):
                    return False
                offset += 1
        # Independent signed-literal translation: NOT x = 1 + x over GF(2).
        expected_mask, expected_rhs = 0, 1
        for literal in cover:
            expected_mask ^= 1 << (abs(literal) - 1)
            if literal < 0:
                expected_rhs = 1 - expected_rhs
        row = cut.get("equation")
        if not _equation(row, n) or row != [expected_mask, expected_rhs]:
            return False
        rows.append((row[0], row[1]))

    contradiction = certificate["contradiction"]
    if contradiction is None:
        return True
    if not isinstance(contradiction, dict):
        return False
    claimed_row = contradiction.get("equation")
    if not _equation(claimed_row, n) or claimed_row != [0, 1]:
        return False
    combination = contradiction.get("combination")
    if not isinstance(combination, list) or not combination or len(combination) > len(rows):
        return False
    if any(type(index) is not int or not 0 <= index < len(rows) for index in combination):
        return False
    if combination != sorted(set(combination)):
        return False
    mask = rhs = 0
    for index in combination:
        mask ^= rows[index][0]
        rhs ^= rows[index][1]
    return mask == 0 and rhs == 1


def solve_with_parity_cuts(
    affine: AffineRelation,
    cnf: Iterable[Iterable[int]],
    *,
    exhaustive: bool = True,
    max_cells: int | None = None,
    include_trace: bool = True,
    include_certificate: bool = False,
) -> dict[str, Any]:
    """Add checked parity consequences, then use the exact quotient solver.

    Flags have solve_mixed's meanings.  max_cells limits only quotient cells:
    a preprocessing contradiction can give UNSAT even with max_cells=0.
    The polynomial cut derivation is always returned under preprocessing;
    include_certificate additionally requests a full final UNSAT envelope,
    whose residual quotient proof can be exponential.  Original CNF clauses
    remain present, so model counts refer to original assignments.
    """
    raw_cnf = _problem(affine, cnf)
    if any(type(flag) is not bool for flag in (exhaustive, include_trace, include_certificate)):
        raise ValueError("Solver flags must be booleans.")
    if max_cells is not None and (type(max_cells) is not int or max_cells < 0):
        raise ValueError("max_cells must be None or a nonnegative integer.")
    derivation = derive_parity_cuts(affine, raw_cnf)
    if not check_parity_cut_certificate(affine, raw_cnf, derivation):
        raise AssertionError("Generated parity-cut certificate failed independent checking.")
    contradiction = derivation["contradiction"] is not None
    if contradiction:
        strengthened = AffineRelation.false(affine.variables)
    else:
        rows = affine.equations + tuple(tuple(cut["equation"]) for cut in derivation["cuts"])
        strengthened = AffineRelation(affine.variables, rows)
        if not strengthened.is_consistent:
            raise AssertionError("Provenance elimination missed a linear contradiction.")
    result = solve_mixed(strengthened, raw_cnf, exhaustive=exhaustive, max_cells=max_cells,
                         include_trace=include_trace, include_certificate=include_certificate)
    if contradiction:
        result["reason"] = "certified_linear_contradiction"
    n = len(affine.variables)
    result["preprocessing"] = {
        "method": "exactly-one-parity-cuts-v1",
        "derived_cut_count": len(derivation["cuts"]),
        "original_affine_rank": len(affine.equations) if affine.is_consistent else None,
        "original_free_dimension": n - len(affine.equations) if affine.is_consistent else None,
        "strengthened_affine_rank": len(strengthened.equations) if strengthened.is_consistent else None,
        "strengthened_free_dimension": n - len(strengthened.equations) if strengthened.is_consistent else None,
        "contradiction_found": contradiction,
        "certificate_checked": True,
        "fallback_used": not contradiction,
        "derivation": derivation,
    }
    if result["status"] == "SAT" and not check_sat_witness(affine, raw_cnf, result["witness_mask"]):
        raise AssertionError("Strengthened solver returned an invalid original-input witness.")
    if include_certificate and result["status"] == "UNSAT":
        result["certificate"] = {
            "kind": "parity-cuts-unsat-v1",
            "derivation": derivation,
            "residual": None if contradiction else result["certificate"],
        }
    return result


def check_parity_cut_unsat_certificate(
    affine: AffineRelation, cnf: Iterable[Iterable[int]], certificate: Any,
) -> bool:
    """Check a final UNSAT envelope against the ORIGINAL XOR + CNF input.

    A certified linear contradiction needs only cut-premise checks and row
    XOR.  Otherwise, checked cuts are added to the input and the existing
    quotient checker validates the residual enumeration proof.  That branch
    trusts AffineRelation normalization, as the existing checker does, and is
    polynomial in input PLUS certificate size, not necessarily input alone.
    """
    raw_cnf = _problem(affine, cnf)
    if not isinstance(certificate, dict) or certificate.get("kind") != "parity-cuts-unsat-v1":
        return False
    derivation = certificate.get("derivation")
    if not check_parity_cut_certificate(affine, raw_cnf, derivation) or "residual" not in certificate:
        return False
    if derivation["contradiction"] is not None:
        return certificate["residual"] is None
    residual = certificate["residual"]
    if not isinstance(residual, dict) or residual.get("kind") != "affine-quotient-unsat-v1":
        return False
    rows = affine.equations + tuple(tuple(cut["equation"]) for cut in derivation["cuts"])
    strengthened = AffineRelation(affine.variables, rows)
    if not strengthened.is_consistent:
        return False
    return check_unsat_certificate(strengthened, raw_cnf, residual)
