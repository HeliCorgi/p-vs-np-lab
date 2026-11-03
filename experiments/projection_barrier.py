#!/usr/bin/env python3
"""Exact elementary obstruction to bounded-width boundary-relation projection.

For q colors, eliminate the center of a star with q ordered terminals. The
result is NOT allDifferent. Any auxiliary-free CNF over terminal equality or
disequality literals needs a clause of width binomial(q, 2). At fixed q=5,
this excludes widths below ten; it does not exclude every fixed width for a
permanently five-color palette. In the general family, palette size and
terminal count both grow with q. This is an elementary finite-relation fact,
not a Boolean 2-SAT or P-versus-NP result.
"""

from __future__ import annotations

import argparse
import hashlib
from itertools import combinations, product
import json
from math import comb, factorial
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from pnp_lab.relations import (  # noqa: E402
    ColorLiteral,
    FiniteRelation,
    canonical_partitions,
    canonicalize_colors,
    clause_holds,
    conjoin_all,
)


def check(checks: dict[str, bool], name: str, condition: bool) -> None:
    checks[name] = bool(condition)
    if not condition:
        raise RuntimeError(f"projection-barrier check failed: {name}")


def state_key(row: tuple[int, ...]) -> str:
    return "".join(map(str, row))


def analyze_palette(q: int) -> dict:
    if type(q) is not int or not 2 <= q <= 6:
        raise ValueError("the explicit experiment supports 2 <= q <= 6")
    ports = tuple(f"t{i}" for i in range(q))
    center = "x"
    pairs = tuple(combinations(range(q), 2))
    equality_literals = tuple(ColorLiteral(ports[i], ports[j]) for i, j in pairs)
    disequality_literals = tuple(ColorLiteral(ports[i], ports[j], equal=False) for i, j in pairs)
    components = [FiniteRelation.disequality(port, center, q) for port in ports]
    star = conjoin_all(components, color_count=q)
    projected = star.project(ports)

    # Independent brute-force existential check: every boundary and every center
    # color is visited, without using the unused-color characterization.
    direct_rows = set()
    direct_total_extensions = 0
    direct_extension_counts = {}
    for boundary in product(range(q), repeat=q):
        extensions = sum(all(center_color != color for color in boundary) for center_color in range(q))
        direct_extension_counts[boundary] = extensions
        direct_total_extensions += extensions
        if extensions:
            direct_rows.add(boundary)

    canonical_universe = tuple(canonical_partitions(q, max_colors=q))
    canonical_allowed = projected.canonical_rows()
    all_distinct = tuple(range(q))
    distinct_assignment = dict(zip(ports, all_distinct))
    checks: dict[str, bool] = {}
    check(checks, "join_projection_matches_direct_existential_enumeration", projected.rows == frozenset(direct_rows))
    check(checks, "joined_star_rows_match_direct_full_coloring_count", len(star.rows) == direct_total_extensions)
    check(checks, "joined_star_count_matches_q_times_q_minus_one_power_q", len(star.rows) == q * (q - 1) ** q)
    check(checks, "projection_count_matches_q_power_q_minus_factorial_q", len(projected.rows) == q ** q - factorial(q))
    check(checks, "projected_relation_is_color_symmetric", projected.is_color_symmetric())
    check(checks, "canonical_relation_excludes_only_all_distinct", canonical_allowed == tuple(row for row in canonical_universe if row != all_distinct))
    check(checks, "all_center_extension_counts_equal_missing_color_count", all(count == q - len(set(row)) for row, count in direct_extension_counts.items()))
    check(checks, "all_equalities_false_at_excluded_state", not any(literal.evaluate(distinct_assignment) for literal in equality_literals))
    check(checks, "all_disequalities_true_at_excluded_state", all(literal.evaluate(distinct_assignment) for literal in disequality_literals))

    formula_rows = frozenset(
        row for row in product(range(q), repeat=q)
        if clause_holds(equality_literals, dict(zip(ports, row)))
    )
    check(checks, "single_full_equality_clause_is_exact", formula_rows == projected.rows)

    witnesses = []
    for omitted_pair, omitted_literal in zip(pairs, equality_literals):
        i, j = omitted_pair
        raw = list(range(q))
        raw[j] = raw[i]
        witness = canonicalize_colors(raw)
        assignment = dict(zip(ports, witness))
        center_color = q - 1
        true_equalities = [literal.as_dict() for literal in equality_literals if literal.evaluate(assignment)]
        omitted_clause = tuple(literal for literal in equality_literals if literal != omitted_literal)
        valid_witness = (
            witness in projected.rows
            and len(set(witness)) == q - 1
            and all(center_color != color for color in witness)
            and true_equalities == [omitted_literal.as_dict()]
            and not clause_holds(omitted_clause, assignment)
        )
        check(checks, f"single_pair_witness_{i}_{j}", valid_witness)
        witnesses.append({
            "required_equality_literal": omitted_literal.as_dict(),
            "canonical_boundary": state_key(witness),
            "boundary_colors_in_port_order": list(witness),
            "center_color": center_color,
            "only_true_terminal_equality": omitted_literal.as_dict(),
            "extends_to_input_star": True,
            "falsifies_disjunction_of_all_other_equalities": True,
        })

    # For q<=4, also enumerate every normalized clause false at allDistinct.
    # Such clauses contain only positive equality literals, by the check above.
    # There are 2^(q choose 2) of these, not 2^(2*(q choose 2)) arbitrary clauses.
    small_clause_audit = None
    if q <= 4:
        valid_masks = []
        for mask in range(1 << len(equality_literals)):
            literals = tuple(literal for bit, literal in enumerate(equality_literals) if mask & (1 << bit))
            if all(clause_holds(literals, dict(zip(ports, row))) for row in canonical_allowed):
                valid_masks.append(mask)
        check(checks, "exhaustive_false_at_all_distinct_clause_audit", valid_masks == [(1 << len(equality_literals)) - 1])
        small_clause_audit = {
            "clauses_checked": 1 << len(equality_literals),
            "clause_space": "All subsets of terminal equality literals; exactly the normalized clauses false at allDistinct.",
            "valid_clause_count": len(valid_masks),
            "unique_valid_clause": "the disjunction of every terminal-pair equality",
        }

    width = comb(q, 2)
    return {
        "q": q,
        "ports_in_order": list(ports),
        "internal_variables": [center],
        "input_binary_disequality_constraints": [[port, center] for port in ports],
        "input_constraint_count": q,
        "input_labeled_assignments_checked_directly": q ** (q + 1),
        "input_proper_colorings": len(star.rows),
        "boundary_labeled_assignments": q ** q,
        "boundary_allowed_labeled_assignments": len(projected.rows),
        "boundary_excluded_labeled_assignments": factorial(q),
        "canonical_boundary_states": len(canonical_universe),
        "canonical_allowed_states": len(canonical_allowed),
        "allowed_canonical_states": [state_key(row) for row in canonical_allowed],
        "excluded_canonical_state": state_key(all_distinct),
        "exact_auxiliary_free_cnf": [[literal.as_dict() for literal in equality_literals]],
        "minimum_required_clause_width": width,
        "width_two_auxiliary_free_representation_possible": width <= 2,
        "certificate": {
            "type": "excluded-state-and-single-equality-witnesses",
            "excluded_state": list(all_distinct),
            "all_equality_literals_false_at_excluded_state": True,
            "all_disequality_literals_true_at_excluded_state": True,
            "single_pair_witnesses": witnesses,
            "witness_count": len(witnesses),
            "reasoning": [
                "A CNF excluding allDistinct has a clause false at that state.",
                "Every disequality is true there, so that false clause can contain only equality literals.",
                "For each terminal pair, its witness is allowed and makes exactly that pair equality true.",
                "A valid false-at-allDistinct clause must therefore include every pair equality.",
                "The full disjunction is exact, proving both the lower and upper width bounds.",
            ],
        },
        "small_clause_exhaustion": small_clause_audit,
        "checks": checks,
        "all_checks_passed": all(checks.values()),
    }


def build_report(color_counts: tuple[int, ...] = (3, 4, 5, 6)) -> dict:
    if len(set(color_counts)) != len(color_counts):
        raise ValueError("color counts must be distinct")
    cases = [analyze_palette(q) for q in sorted(color_counts)]
    source_paths = ("src/pnp_lab/relations.py", "experiments/projection_barrier.py")
    return {
        "schema_version": 1,
        "experiment": "projection_barrier",
        "status": "ELEMENTARY-PROJECTION-WIDTH-OBSTRUCTION-VERIFIED",
        "provenance": {
            "inputs": "Explicit q-terminal star family, q colors, center x adjacent to every terminal.",
            "randomness": "none",
            "external_inputs": [],
            "source_sha256": {
                path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in source_paths
            },
            "canonicalization": "First-occurrence color renaming preserves terminal order; joins use labeled rows.",
            "named_color_pinnings": "None in this experiment. Generic relations retain labels and reject asymmetric canonical summaries.",
        },
        "claim_scope": (
            "An elementary, exact representational obstruction: for each checked palette q, "
            "this projection requires a clause of width q*(q-1)/2 in auxiliary-free CNF "
            "over terminal-pair color equality/disequality predicates. At fixed q=5 this "
            "rules out widths below ten, including width two. A bound uniform over the "
            "general q family fails when BOTH palette size and terminal count grow. "
            "No novelty claim, Boolean 2-SAT claim, "
            "algorithmic running-time lower bound, graph-coloring complexity separation, "
            "or P-versus-NP conclusion is made."
        ),
        "fixed_palette_limit": (
            "This star family does not rule out every fixed clause width while the palette "
            "remains five colors and only the number of terminals grows. Its five-color "
            "example has an exact width-ten clause."
        ),
        "auxiliary_variable_qualification": (
            "Retaining the existential center x keeps a representation using q binary "
            "disequality constraints. The width obstruction applies only after eliminating "
            "auxiliaries and restricting literals to terminal-pair equality/disequality."
        ),
        "cases": cases,
        "all_checks_passed": all(case["all_checks_passed"] for case in cases),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    parser.add_argument("--colors", type=int, nargs="+", default=[3, 4, 5, 6], help="Explicit palettes to check (2..6).")
    args = parser.parse_args()
    report = build_report(tuple(args.colors))
    args.out_dir.mkdir(parents=True, exist_ok=True)
    output = args.out_dir / "projection_barrier.json"
    output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "all_checks_passed": report["all_checks_passed"],
        "cases": [{
            "q": case["q"],
            "canonical_states": case["canonical_boundary_states"],
            "allowed_states": case["canonical_allowed_states"],
            "minimum_clause_width": case["minimum_required_clause_width"],
        } for case in report["cases"]],
        "output": str(output),
    }, indent=2))


if __name__ == "__main__":
    main()
