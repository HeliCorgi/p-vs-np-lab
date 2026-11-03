"""Exact counting by group-local CNF tables and GF(2) XOR signatures.

This is a finite conditioning/sum-product specialization, not the upstream
openai/math subexponential algorithm. Every non-tautological CNF clause must
fit inside one explicitly supplied group. XOR equations may cross groups.
Table construction and convolution can both be exponential; their actual
assignment visits, table sizes, and pair products are reported separately.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from typing import Any

from .affine import AffineRelation
from .mixed import _normalize_cnf, _problem, check_sat_witness


def _partition(variables: tuple[str, ...], groups: Iterable[Sequence[str]]) -> tuple[tuple[str, ...], ...]:
    """Read an ordered partition; empty groups are harmless and permitted."""
    if isinstance(groups, (str, bytes)):
        raise ValueError("groups must be an iterable of groups of variable names.")
    try:
        supplied = tuple(groups)
    except TypeError as error:
        raise ValueError("groups must be an iterable of groups of variable names.") from error
    known = set(variables)
    seen: set[str] = set()
    normalized = []
    for group in supplied:
        if isinstance(group, (str, bytes)):
            raise ValueError("Each group must contain variable names, not one string.")
        try:
            names = tuple(group)
        except TypeError as error:
            raise ValueError("Each group must be an iterable of variable names.") from error
        for name in names:
            if not isinstance(name, str) or name not in known:
                raise ValueError(f"Unknown group variable: {name!r}")
            if name in seen:
                raise ValueError(f"Groups must be disjoint; repeated variable: {name!r}")
            seen.add(name)
        normalized.append(names)
    if seen != known:
        raise ValueError(f"Groups must cover the explicit scope; missing: {sorted(known - seen)!r}")
    return tuple(normalized)


def count_by_signatures(
    affine: AffineRelation,
    cnf: Iterable[Iterable[int]],
    groups: Iterable[Sequence[str]],
    *,
    max_group_assignments: int | None = None,
    max_join_products: int | None = None,
) -> dict[str, Any]:
    """Count every model or return UNKNOWN if an explicit work budget runs out.

    DIMACS literals refer to ``affine.variables``. Groups partition that same
    explicit scope by NAME, with caller-specified order. A normalized clause
    crossing groups raises ValueError, including on otherwise UNSAT inputs.
    Empty clauses and inconsistent XORs are detected after input validation.

    The two budgets count totals across all groups: tested local assignments,
    and pairs of nonzero table entries multiplied in the successive joins.
    Merely reaching a budget exactly does not interrupt a completed stage.
    Partial tables never justify an exact count, SAT, or UNSAT answer. An
    empty completed local table, however, proves a zero count immediately.

    Signature bit j is the local contribution to normalized input XOR row j.
    Exact integer multiplicities and one original-variable representative
    are retained per signature. The returned witness is a full assignment
    in the original explicit scope. Tables themselves are not serialized.
    """
    raw_cnf = _problem(affine, cnf)
    for label, budget in (("max_group_assignments", max_group_assignments),
                          ("max_join_products", max_join_products)):
        if budget is not None and (type(budget) is not int or budget < 0):
            raise ValueError(f"{label} must be None or a nonnegative integer.")
    partition = _partition(affine.variables, groups)
    normalized = _normalize_cnf(raw_cnf)
    positions = {name: i for i, name in enumerate(affine.variables)}
    columns = tuple(tuple(positions[name] for name in group) for group in partition)
    owner = {column: index for index, group in enumerate(columns) for column in group}
    clause_masks: list[list[tuple[int, int]]] = [[] for _ in partition]
    has_empty_clause = False
    for clause in normalized:
        if not clause:
            has_empty_clause = True
            continue
        owners = {owner[abs(literal) - 1] for literal in clause}
        if len(owners) != 1:
            raise ValueError("Unsupported cross-group CNF clause: every non-tautological "
                             f"clause must fit in one group; got {clause!r}.")
        positive = sum(1 << (literal - 1) for literal in clause if literal > 0)
        negative = sum(1 << (-literal - 1) for literal in clause if literal < 0)
        clause_masks[next(iter(owners))].append((positive, negative))

    n = len(affine.variables)
    m = len(affine.equations)
    target = sum(rhs << j for j, (_, rhs) in enumerate(affine.equations))
    group_count = len(partition)
    result: dict[str, Any] = {
        "status": "UNKNOWN", "reason": None, "exhaustive": False,
        "model_count": None, "witness_mask": None, "witness": None,
        "n_variables": n, "n_groups": group_count,
        "groups": [list(group) for group in partition],
        "group_sizes": [len(group) for group in partition],
        "max_block_size": max((len(group) for group in partition), default=0),
        "input_clause_count": len(raw_cnf), "normalized_clause_count": len(normalized),
        "affine_consistent": affine.is_consistent,
        "input_affine_row_count": m, "signature_bits": m, "target_signature": target,
        "group_assignments_tested": 0,
        "group_assignments_tested_by_group": [0] * group_count,
        "group_valid_assignment_counts": [0] * group_count,
        "group_signature_counts": [0] * group_count,
        "group_tables_complete": [False] * group_count,
        "dp_state_counts": [1], "dp_states_peak": 1,
        "join_products": 0, "join_products_by_group": [0] * group_count,
        "join_groups_completed": 0,
        "join_partial_group_index": None, "join_partial_state_count": None,
        "max_group_assignments": max_group_assignments,
        "max_join_products": max_join_products,
    }
    if not affine.is_consistent:
        result.update(status="UNSAT", reason="inconsistent_xor", exhaustive=True, model_count=0)
        return result
    if has_empty_clause:
        result.update(status="UNSAT", reason="empty_cnf_clause", exhaustive=True, model_count=0)
        return result

    # Value = (exact positive multiplicity, one original-scope witness mask).
    tables: list[dict[int, tuple[int, int]]] = []
    for group_index, group_columns in enumerate(columns):
        table: dict[int, tuple[int, int]] = {}
        for local_assignment in range(1 << len(group_columns)):
            if (max_group_assignments is not None
                    and result["group_assignments_tested"] >= max_group_assignments):
                result.update(reason="group_assignment_budget_exhausted")
                return result
            result["group_assignments_tested"] += 1
            result["group_assignments_tested_by_group"][group_index] += 1
            assignment = sum(((local_assignment >> local) & 1) << column
                             for local, column in enumerate(group_columns))
            if any(not ((assignment & positive) or ((~assignment) & negative))
                   for positive, negative in clause_masks[group_index]):
                continue
            result["group_valid_assignment_counts"][group_index] += 1
            signature = sum(((mask & assignment).bit_count() & 1) << j
                            for j, (mask, _) in enumerate(affine.equations))
            if signature in table:
                multiplicity, witness = table[signature]
                table[signature] = (multiplicity + 1, witness)
            else:
                table[signature] = (1, assignment)
                result["group_signature_counts"][group_index] += 1
        result["group_tables_complete"][group_index] = True
        if not table:
            result.update(status="UNSAT", reason="group_cnf_unsatisfiable",
                          exhaustive=True, model_count=0)
            return result
        tables.append(table)

    dynamic: dict[int, tuple[int, int]] = {0: (1, 0)}
    for group_index, table in enumerate(tables):
        joined: dict[int, tuple[int, int]] = {}
        for old_signature, (old_count, old_witness) in dynamic.items():
            for local_signature, (local_count, local_witness) in table.items():
                if (max_join_products is not None
                        and result["join_products"] >= max_join_products):
                    result.update(reason="join_product_budget_exhausted",
                                  join_partial_group_index=group_index,
                                  join_partial_state_count=len(joined))
                    return result
                result["join_products"] += 1
                result["join_products_by_group"][group_index] += 1
                signature = old_signature ^ local_signature
                product_count = old_count * local_count
                if signature in joined:
                    previous_count, witness = joined[signature]
                    joined[signature] = (previous_count + product_count, witness)
                else:
                    joined[signature] = (product_count, old_witness | local_witness)
                    result["dp_states_peak"] = max(result["dp_states_peak"], len(joined))
        dynamic = joined
        result["join_groups_completed"] += 1
        result["dp_state_counts"].append(len(dynamic))

    model_count, witness = dynamic.get(target, (0, None))
    result.update(status="SAT" if model_count else "UNSAT", reason="signature_sum_complete",
                  exhaustive=True, model_count=model_count)
    if model_count:
        result["witness_mask"] = witness
        result["witness"] = {name: (witness >> i) & 1 for i, name in enumerate(affine.variables)}
        if not check_sat_witness(affine, raw_cnf, witness):
            raise AssertionError("Signature counting returned an invalid original-input witness.")
    return result
