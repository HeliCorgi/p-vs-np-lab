"""Checked clauses derived jointly from XOR rows and binary CNF premises.

For each variable in a normalized XOR row, choose a binary clause containing
a signed literal of that variable. If falsifying all other (partner) literals
would force the row to have the wrong parity, their disjunction is implied.
The fixed width cap is THREE; it is not an uncharged input parameter. Only
input rows and input binary clauses are searched, in one pass. Original
constraints remain present, so adding the checked clauses preserves models.

The exact solver then applies the previous exactly-one parity cuts. Neither
preprocessing stage makes the residual quotient search polynomial in general.
Input XOR normalization and the Python runtime remain trusted as documented
for AffineRelation. Clause checking does not rerun inference discovery or
Gaussian elimination. Candidate counters describe the producer's work; they
are not certificates that every possible consequence has been discovered.
"""

from __future__ import annotations

from collections.abc import Iterable
from itertools import product
from math import comb
from typing import Any

from .affine import AffineRelation
from .mixed import CNF, _normalize_cnf, _problem, check_sat_witness
from .parity_cuts import check_parity_cut_unsat_certificate, solve_with_parity_cuts


MAX_JOINT_ROW_WIDTH = 3


def _support(mask: int) -> tuple[int, ...]:
    columns = []
    while mask:
        lowest = mask & -mask
        columns.append(lowest.bit_length() - 1)
        mask ^= lowest
    return tuple(columns)


def derive_joint_clauses(
    affine: AffineRelation, cnf: Iterable[Iterable[int]],
) -> dict[str, Any]:
    """Return original-premise proofs of new clauses, using row width <= 3.

    Premises are ordered by increasing variable index in the cited input XOR
    row. A premise names its signed pivot literal and a zero-based raw CNF
    clause index. Its other literal is a partner. Repeated partners collapse
    in the derived disjunction; tautological or already present outputs are
    omitted. A contradictory empty XOR row can derive the empty clause.
    """
    raw_cnf = _problem(affine, cnf)
    existing = set(_normalize_cnf(raw_cnf))
    first_binary: dict[frozenset[int], int] = {}
    for index, clause in enumerate(raw_cnf):
        literals = frozenset(clause)
        if len(literals) == 2 and not any(-lit in literals for lit in literals):
            first_binary.setdefault(literals, index)
    choices: dict[int, list[tuple[int, int, int]]] = {}
    for literals, index in first_binary.items():
        left, right = sorted(literals, key=lambda lit: (abs(lit), lit))
        choices.setdefault(abs(left) - 1, []).append((left, right, index))
        choices.setdefault(abs(right) - 1, []).append((right, left, index))

    deductions = []
    seen = set(existing)
    examined = 0
    for row_index, (mask, rhs) in enumerate(affine.equations):
        columns = _support(mask)
        if len(columns) > MAX_JOINT_ROW_WIDTH:
            continue
        options = [choices.get(column, ()) for column in columns]
        for selected in product(*options):
            examined += 1
            forced_parity = sum(pivot > 0 for pivot, _, _ in selected) % 2
            if forced_parity == rhs:
                continue
            normalized = _normalize_cnf((tuple(partner for _, partner, _ in selected),))
            if not normalized:
                continue
            conclusion = normalized[0]
            if conclusion in seen:
                continue
            seen.add(conclusion)
            deductions.append({
                "xor_row": row_index,
                "premises": [{"pivot_literal": pivot, "clause": index}
                             for pivot, _, index in selected],
                "clause": list(conclusion),
            })
    return {
        "kind": "joint-xor-binary-clauses-v1",
        "n_variables": len(affine.variables),
        "input_clause_count": len(raw_cnf),
        "input_affine_row_count": len(affine.equations),
        "max_row_width": MAX_JOINT_ROW_WIDTH,
        "candidates_examined": examined,
        "clauses": deductions,
    }


def _checked_clause(raw_cnf: CNF, index: Any) -> tuple[int, ...] | None:
    """Checker-side support normalization, independent of the producer."""
    if type(index) is not int or not 0 <= index < len(raw_cnf):
        return None
    literals = []
    for literal in raw_cnf[index]:
        if -literal in literals:
            return None
        if literal not in literals:
            literals.append(literal)
    return tuple(sorted(literals, key=lambda lit: (abs(lit), lit)))


def check_joint_clause_certificate(
    affine: AffineRelation, cnf: Iterable[Iterable[int]], certificate: Any,
) -> bool:
    """Validate each supplied implication against ORIGINAL XOR and CNF input.

    No inference finder, solver, row-space enumeration or Gaussian elimination
    is invoked. This proves sound strengthening only, not SAT/UNSAT or that all
    eligible consequences were found. Discovery counters are range-checked,
    but are not independently recomputed. Invalid input raises ValueError;
    a malformed proof of a valid input returns False.
    """
    raw_cnf = _problem(affine, cnf)
    if not isinstance(certificate, dict) or certificate.get("kind") != "joint-xor-binary-clauses-v1":
        return False
    n = len(affine.variables)
    rows = affine.equations
    for field, expected in (("n_variables", n), ("input_clause_count", len(raw_cnf)),
                            ("input_affine_row_count", len(rows)),
                            ("max_row_width", MAX_JOINT_ROW_WIDTH)):
        if type(certificate.get(field)) is not int or certificate[field] != expected:
            return False
    examined = certificate.get("candidates_examined")
    candidate_bound = len(rows) * max(1, len(raw_cnf)) ** MAX_JOINT_ROW_WIDTH
    if type(examined) is not int or not 0 <= examined <= candidate_bound:
        return False
    deductions = certificate.get("clauses")
    # With fixed width, even the number of distinct possible conclusions is
    # polynomial. This bound includes the empty clause and small scopes.
    conclusion_bound = sum((1 << width) * comb(n, width)
                           for width in range(min(n, MAX_JOINT_ROW_WIDTH) + 1))
    if (not isinstance(deductions, list)
            or len(deductions) > min(examined, conclusion_bound)):
        return False
    seen = set()
    for deduction in deductions:
        if not isinstance(deduction, dict):
            return False
        index = deduction.get("xor_row")
        if type(index) is not int or not 0 <= index < len(rows):
            return False
        mask, rhs = rows[index]
        # Deliberately compute support independently of the producer's helper.
        columns = [column for column in range(n) if (mask >> column) & 1]
        if len(columns) > MAX_JOINT_ROW_WIDTH:
            return False
        premises = deduction.get("premises")
        if not isinstance(premises, list) or len(premises) != len(columns):
            return False
        partners = []
        forced = 0
        for column, premise in zip(columns, premises):
            if not isinstance(premise, dict):
                return False
            pivot = premise.get("pivot_literal")
            if type(pivot) is not int or abs(pivot) != column + 1:
                return False
            clause = _checked_clause(raw_cnf, premise.get("clause"))
            if clause is None or len(clause) != 2 or pivot not in clause:
                return False
            partner = clause[1] if clause[0] == pivot else clause[0]
            partners.append(partner)
            forced ^= 1 if pivot > 0 else 0
        if forced == rhs:
            return False
        normalized = []
        for partner in partners:
            if -partner in normalized:
                return False  # This checker accepts only non-tautological outputs.
            if partner not in normalized:
                normalized.append(partner)
        normalized.sort(key=lambda lit: (abs(lit), lit))
        claimed = deduction.get("clause")
        if (not isinstance(claimed, list) or any(type(lit) is not int for lit in claimed)
                or claimed != normalized or tuple(normalized) in seen):
            return False
        seen.add(tuple(normalized))
    return True


def solve_with_joint_reasoning(
    affine: AffineRelation,
    cnf: Iterable[Iterable[int]],
    *,
    exhaustive: bool = True,
    max_cells: int | None = None,
    include_trace: bool = True,
    include_certificate: bool = False,
) -> dict[str, Any]:
    """Add checked joint clauses, then checked parity cuts, then exact search.

    max_cells bounds only representative enumeration. Both polynomial
    preprocessing passes can prove UNSAT at budget zero. All original
    variables and constraints remain; witnesses and counts concern original
    assignments. A full residual UNSAT certificate may be exponential.
    """
    raw_cnf = _problem(affine, cnf)
    if any(type(flag) is not bool for flag in (exhaustive, include_trace, include_certificate)):
        raise ValueError("Solver flags must be booleans.")
    if max_cells is not None and (type(max_cells) is not int or max_cells < 0):
        raise ValueError("max_cells must be None or a nonnegative integer.")
    derivation = derive_joint_clauses(affine, raw_cnf)
    if not check_joint_clause_certificate(affine, raw_cnf, derivation):
        raise AssertionError("Generated joint-clause certificate failed independent checking.")
    augmented = raw_cnf + tuple(tuple(step["clause"]) for step in derivation["clauses"])
    result = solve_with_parity_cuts(
        affine, augmented, exhaustive=exhaustive, max_cells=max_cells,
        include_trace=include_trace, include_certificate=include_certificate,
    )
    result["joint_preprocessing"] = {
        "method": "bounded-xor-binary-v1",
        "max_row_width": MAX_JOINT_ROW_WIDTH,
        "eligible_xor_row_count": sum(mask.bit_count() <= MAX_JOINT_ROW_WIDTH
                                      for mask, _ in affine.equations),
        "candidates_examined": derivation["candidates_examined"],
        "derived_clause_count": len(derivation["clauses"]),
        "original_clause_count": len(raw_cnf),
        "augmented_clause_count": len(augmented),
        "certificate_checked": True,
        "derivation": derivation,
    }
    if result["status"] == "SAT" and not check_sat_witness(affine, raw_cnf, result["witness_mask"]):
        raise AssertionError("Joint solver returned an invalid original-input witness.")
    if include_certificate and result["status"] == "UNSAT":
        result["certificate"] = {
            "kind": "joint-xor-cnf-unsat-v1",
            "joint_derivation": derivation,
            "residual": result["certificate"],
        }
    return result


def check_joint_unsat_certificate(
    affine: AffineRelation, cnf: Iterable[Iterable[int]], certificate: Any,
) -> bool:
    """Check the composed UNSAT proof against ORIGINAL CNF+XOR input.

    Checked joint clauses reconstruct the augmented CNF, after which the
    existing parity-cut checker validates its proof. A linear contradiction
    uses only cited row XOR; a residual quotient proof retains that checker's
    documented normalization trust and may have exponential length.
    """
    raw_cnf = _problem(affine, cnf)
    if not isinstance(certificate, dict) or certificate.get("kind") != "joint-xor-cnf-unsat-v1":
        return False
    derivation = certificate.get("joint_derivation")
    if not check_joint_clause_certificate(affine, raw_cnf, derivation) or "residual" not in certificate:
        return False
    augmented = raw_cnf + tuple(tuple(step["clause"]) for step in derivation["clauses"])
    return check_parity_cut_unsat_certificate(affine, augmented, certificate["residual"])
