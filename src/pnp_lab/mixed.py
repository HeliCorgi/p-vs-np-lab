"""Exact XOR + CNF solving by enumeration of an observed affine quotient.

DIMACS literal +/-i refers to affine.variables[i - 1].  The scope is explicit,
including unconstrained variables.  The rank parameter is the rank of the
affine coefficient forms of variables in non-tautological CNF clauses.  It is
an observation rank, not a minimum measure of nonlinearity.

No implicit resource limit is imposed.  An explicit cell budget may return
UNKNOWN; it never turns an incomplete search into UNSAT.  Full UNSAT
certificates are opt-in and can be exponentially large.  See
docs/mixed_solver.md for the proof, bit-cost accounting, and trust boundary.
"""

from __future__ import annotations

from collections.abc import Iterable
from typing import Any

from .affine import AffineRelation


CNF = tuple[tuple[int, ...], ...]


def _read_cnf(cnf: Iterable[Iterable[int]], n: int) -> CNF:
    """Validate before normalization, including literals in tautologies."""
    if isinstance(cnf, (str, bytes)):
        raise ValueError("CNF must be an iterable of clauses.")
    try:
        clauses_list = []
        for clause in cnf:
            if isinstance(clause, (str, bytes)):
                raise ValueError("A clause must contain integer literals, not text.")
            clauses_list.append(tuple(clause))
        clauses = tuple(clauses_list)
    except TypeError as error:
        raise ValueError("Each CNF clause must be an iterable of literals.") from error
    for clause in clauses:
        for literal in clause:
            if type(literal) is not int or not 1 <= abs(literal) <= n:
                raise ValueError("DIMACS literals must be nonzero integers within the explicit scope.")
    return clauses


def _normalize_cnf(cnf: CNF) -> CNF:
    """Remove tautologies and duplicates; preserve an empty (false) clause."""
    clauses = []
    seen = set()
    for clause in cnf:
        literals = set(clause)
        if any(-literal in literals for literal in literals):
            continue
        normalized = tuple(sorted(literals, key=lambda value: (abs(value), value)))
        if normalized not in seen:
            seen.add(normalized)
            clauses.append(normalized)
    return tuple(clauses)


def _problem(affine: AffineRelation, cnf: Iterable[Iterable[int]]) -> CNF:
    if not isinstance(affine, AffineRelation):
        raise ValueError("The XOR input must be an AffineRelation with an explicit variable scope.")
    return _read_cnf(cnf, len(affine.variables))


def _parameterize(affine: AffineRelation) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    """Read the public normalized RREF, producing x_i = c_i + <a_i,t>."""
    n = len(affine.variables)
    pivot_columns = tuple((mask & -mask).bit_length() - 1 for mask, _ in affine.equations)
    pivot_set = set(pivot_columns)
    free_columns = tuple(column for column in range(n) if column not in pivot_set)
    forms = [0] * n
    for parameter, column in enumerate(free_columns):
        forms[column] = 1 << parameter
    base_point = 0
    for (mask, rhs), pivot in zip(affine.equations, pivot_columns):
        base_point |= rhs << pivot
        forms[pivot] = sum(1 << parameter for parameter, column in enumerate(free_columns)
                           if (mask >> column) & 1)
    return base_point, tuple(forms), free_columns


def _observation_basis(forms: Iterable[int], d: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """RREF of coefficient forms; pivot unit vectors give a right inverse."""
    rows = list(forms)
    pivots = []
    rank = 0
    for column in range(d):
        pivot = next((i for i in range(rank, len(rows)) if (rows[i] >> column) & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(len(rows)):
            if i != rank and (rows[i] >> column) & 1:
                rows[i] ^= rows[rank]
        pivots.append(column)
        rank += 1
    return tuple(rows[:rank]), tuple(1 << column for column in pivots)


def _xor_selected(vectors: Iterable[int], selector: int) -> int:
    result = 0
    for index, vector in enumerate(vectors):
        if (selector >> index) & 1:
            result ^= vector
    return result


def _lift(base_point: int, forms: tuple[int, ...], free_assignment: int) -> int:
    result = base_point
    for column, form in enumerate(forms):
        result ^= ((form & free_assignment).bit_count() & 1) << column
    return result


def _clause_masks(cnf: CNF) -> tuple[tuple[int, int], ...]:
    result = []
    for clause in cnf:
        positive = negative = 0
        for literal in clause:
            if literal > 0:
                positive |= 1 << (literal - 1)
            else:
                negative |= 1 << (-literal - 1)
        result.append((positive, negative))
    return tuple(result)


def solve_mixed(
    affine: AffineRelation,
    cnf: Iterable[Iterable[int]],
    *,
    exhaustive: bool = True,
    max_cells: int | None = None,
    include_trace: bool = True,
    include_certificate: bool = False,
) -> dict[str, Any]:
    """Decide any finite XOR + CNF input, or return UNKNOWN on a cell budget.

    With exhaustive=True and sufficient budget, also count all models.  With
    exhaustive=False, stop at the first SAT witness.  Trace rows count TRUE
    clauses in the ORIGINAL CNF, including duplicate and tautological clauses.
    include_certificate independently requests a full UNSAT proof object;
    disabling both output flags keeps working storage polynomial in the input.
    """
    raw_cnf = _problem(affine, cnf)
    if any(type(flag) is not bool for flag in (exhaustive, include_trace, include_certificate)):
        raise ValueError("Solver flags must be booleans.")
    if max_cells is not None and (type(max_cells) is not int or max_cells < 0):
        raise ValueError("max_cells must be None or a nonnegative integer.")
    normalized = _normalize_cnf(raw_cnf)
    n = len(affine.variables)
    observed = tuple(sorted({abs(literal) - 1 for clause in normalized for literal in clause}))
    result: dict[str, Any] = {
        "status": "UNKNOWN",
        "n_variables": n,
        "affine_consistent": affine.is_consistent,
        "affine_dimension": None,
        "effective_rank": None,
        "quotient_cells": 0,
        "checked_cells": 0,
        "exhaustive": False,
        "requested_exhaustive": exhaustive,
        "satisfying_cells": 0,
        "rejecting_cells": 0,
        "model_count": None,
        "witness_mask": None,
        "witness": None,
        "input_clause_count": len(raw_cnf),
        "normalized_clause_count": len(normalized),
        "observed_variables": [affine.variables[i] for i in observed],
        "trace_included": include_trace,
        "trace": [],
        "certificate": None,
    }
    if not affine.is_consistent:
        result.update(status="UNSAT", exhaustive=True, model_count=0, reason="inconsistent_xor")
        if include_certificate:
            result["certificate"] = {"kind": "inconsistent-affine-v1", "equation": [0, 1]}
        return result

    base_point, forms, free_columns = _parameterize(affine)
    d = len(free_columns)
    basis, right_inverse = _observation_basis((forms[i] for i in observed), d)
    r = len(basis)
    total = 1 << r
    result.update(affine_dimension=d, effective_rank=r, quotient_cells=total,
                  free_variables=[affine.variables[i] for i in free_columns],
                  omitted_affine_directions=d - r)
    masks = _clause_masks(raw_cnf)
    cells = []
    limit = total if max_cells is None else min(total, max_cells)
    for cell in range(limit):
        free_assignment = _xor_selected(right_inverse, cell)
        assignment = _lift(base_point, forms, free_assignment)
        true_clauses = sum(bool((assignment & positive) or ((~assignment) & negative))
                           for positive, negative in masks)
        satisfies = true_clauses == len(raw_cnf)
        result["checked_cells"] += 1
        result["satisfying_cells" if satisfies else "rejecting_cells"] += 1
        if include_trace or include_certificate:
            cells.append({"cell": cell, "free_assignment_mask": free_assignment,
                          "assignment_mask": assignment, "satisfied_clause_count": true_clauses,
                          "satisfies_cnf": satisfies})
        if satisfies and result["witness_mask"] is None:
            result["witness_mask"] = assignment
            result["witness"] = {name: (assignment >> i) & 1 for i, name in enumerate(affine.variables)}
        if satisfies and not exhaustive:
            break

    complete = result["checked_cells"] == total
    result["exhaustive"] = complete
    if result["witness_mask"] is not None:
        result.update(status="SAT", reason="witness_found")
    elif complete:
        result.update(status="UNSAT", reason="all_quotient_cells_rejected")
    else:
        result.update(status="UNKNOWN", reason="cell_budget_exhausted")
    if complete:
        result["model_count"] = result["satisfying_cells"] * (1 << (d - r))
    if include_trace:
        result["trace"] = cells
    if include_certificate and result["status"] == "UNSAT":
        result["certificate"] = {
            "kind": "affine-quotient-unsat-v1",
            "n_variables": n, "affine_dimension": d, "effective_rank": r,
            "base_point": base_point, "variable_forms": list(forms),
            "observation_basis": list(basis), "right_inverse": list(right_inverse),
            "checked_cells": total, "satisfying_cells": 0, "rejecting_cells": total,
            "cells": cells,
        }
    return result


def _direct_cnf_count(cnf: CNF, assignment: int) -> int:
    """Literal-by-literal evaluation, separate from the solver's clause masks."""
    return sum(any(((assignment >> (abs(literal) - 1)) & 1) == int(literal > 0)
                   for literal in clause) for clause in cnf)


def check_sat_witness(affine: AffineRelation, cnf: Iterable[Iterable[int]], witness_mask: int) -> bool:
    """Check normalized input XOR rows and original CNF directly; no solving."""
    raw_cnf = _problem(affine, cnf)
    n = len(affine.variables)
    if type(witness_mask) is not int or not 0 <= witness_mask < 1 << n:
        return False
    for mask, rhs in affine.equations:
        value = sum((witness_mask >> i) & 1 for i in range(n) if (mask >> i) & 1) % 2
        if value != rhs:
            return False
    return _direct_cnf_count(raw_cnf, witness_mask) == len(raw_cnf)


def _checker_rank(rows: Iterable[int]) -> int:
    """High-pivot echelon rank, independent of the solver's low-pivot RREF."""
    pivots: dict[int, int] = {}
    for original in rows:
        row = original
        while row:
            column = row.bit_length() - 1
            if column in pivots:
                row ^= pivots[column]
            else:
                pivots[column] = row
                break
    return len(pivots)


def _bounded_int(value: Any, width: int) -> bool:
    return type(value) is int and 0 <= value < 1 << width


def check_unsat_certificate(
    affine: AffineRelation, cnf: Iterable[Iterable[int]], certificate: Any,
) -> bool:
    """Check an explicit UNSAT proof, without rerunning the solver/compiler.

    The proof contains an onto affine parameterization, a full-rank observation
    map and its right inverse, and every rejecting quotient cell.  Validation
    is polynomial in input PLUS certificate size; that size can be exponential.
    This Python checker and AffineRelation normalization are trusted code, not
    a claim of end-to-end formal verification.  A missing certificate is False.
    """
    raw_cnf = _problem(affine, cnf)
    if not isinstance(certificate, dict):
        return False
    if certificate.get("kind") == "inconsistent-affine-v1":
        return (affine.equations == ((0, 1),)
                and certificate.get("equation") == [0, 1])
    if certificate.get("kind") != "affine-quotient-unsat-v1" or not affine.is_consistent:
        return False
    n = len(affine.variables)
    if type(certificate.get("n_variables")) is not int or certificate["n_variables"] != n:
        return False
    d, r = certificate.get("affine_dimension"), certificate.get("effective_rank")
    if type(d) is not int or type(r) is not int or not 0 <= r <= d <= n:
        return False
    if d != n - _checker_rank(mask for mask, _ in affine.equations):
        return False
    base = certificate.get("base_point")
    forms = certificate.get("variable_forms")
    basis = certificate.get("observation_basis")
    lifts = certificate.get("right_inverse")
    if not _bounded_int(base, n):
        return False
    for vectors, length in ((forms, n), (basis, r), (lifts, r)):
        if not isinstance(vectors, list) or len(vectors) != length:
            return False
        if any(not _bounded_int(value, d) for value in vectors):
            return False

    # A d-dimensional injective affine map into the input solution set is onto.
    if _checker_rank(forms) != d:
        return False
    for mask, rhs in affine.equations:
        constant = sum((base >> i) & 1 for i in range(n) if (mask >> i) & 1) % 2
        coefficient = 0
        for i in range(n):
            if (mask >> i) & 1:
                coefficient ^= forms[i]
        if constant != rhs or coefficient:
            return False

    # Every clause either is a tautology or observes only the claimed span.
    observed_forms = []
    for clause in raw_cnf:
        literals = set(clause)
        if any(-literal in literals for literal in literals):
            continue
        observed_forms.extend(forms[abs(literal) - 1] for literal in literals)
    if (_checker_rank(observed_forms) != r or _checker_rank(basis) != r
            or _checker_rank(list(basis) + observed_forms) != r):
        return False
    for i, row in enumerate(basis):
        for j, lift in enumerate(lifts):
            dot = sum(((row >> k) & 1) * ((lift >> k) & 1) for k in range(d)) % 2
            if dot != int(i == j):
                return False

    total = 1 << r
    for key, expected in (("checked_cells", total), ("satisfying_cells", 0), ("rejecting_cells", total)):
        if type(certificate.get(key)) is not int or certificate[key] != expected:
            return False
    cells = certificate.get("cells")
    if not isinstance(cells, list) or len(cells) != total:
        return False
    for expected_cell, record in enumerate(cells):
        if not isinstance(record, dict):
            return False
        cell = record.get("cell")
        free_assignment = record.get("free_assignment_mask")
        assignment = record.get("assignment_mask")
        if type(cell) is not int or cell != expected_cell:
            return False
        if not _bounded_int(free_assignment, d) or not _bounded_int(assignment, n):
            return False
        expected_free = 0
        for j, lift in enumerate(lifts):
            if (cell >> j) & 1:
                expected_free ^= lift
        if free_assignment != expected_free:
            return False
        # Scalar evaluation intentionally does not call the production lift.
        expected_assignment = 0
        for i, form in enumerate(forms):
            bit = ((base >> i) & 1) ^ (sum(((form >> j) & 1) * ((free_assignment >> j) & 1)
                                         for j in range(d)) % 2)
            expected_assignment |= bit << i
        if assignment != expected_assignment:
            return False
        true_count = _direct_cnf_count(raw_cnf, assignment)
        if (true_count == len(raw_cnf) or record.get("satisfies_cnf") is not False
                or type(record.get("satisfied_clause_count")) is not int
                or record["satisfied_clause_count"] != true_count):
            return False
        # Independently check the representative against the input XOR rows.
        if not all(sum((assignment >> i) & 1 for i in range(n) if (mask >> i) & 1) % 2 == rhs
                   for mask, rhs in affine.equations):
            return False
    return True
