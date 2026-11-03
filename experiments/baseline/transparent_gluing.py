#!/usr/bin/env python3
"""Exhaustively check transparent gluing in four tiny abstract 5-color graphs.

The common terminal skeleton is K4 minus the C--D edge, with ordered ports
(A, B, C, D). A tip is an internal vertex adjacent to all four ports. Two
independent tips add no boundary constraint; adding an edge between the tips
removes the four-color boundary state.

All labeled assignments are visited, without SAT solvers, symmetry pruning,
or third-party packages. Canonicalization is used only to summarize results.

Example:
    python transparent_gluing.py --out-dir results/transparent-gluing

This is an abstract finite graph experiment. It does not establish a planar
unit-distance realization, a Hadwiger--Nelson bound, or a complexity separation.
It is separate from the conditional quotient/P2 claims in the upstream repo.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path


K = 5
PORTS = ("A", "B", "C", "D")
SKELETON_EDGES = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3))
SKELETON_RELATION = ("0122", "0123")


@dataclass(frozen=True)
class Case:
    name: str
    tip_count: int
    coupled: bool
    expected_extensions: tuple[int, int]
    expected_proper_total: int


CASES = (
    Case("k4_minus_edge", 0, False, (1, 1), 180),
    Case("one_tip", 1, False, (2, 1), 240),
    Case("two_uncoupled_tips", 2, False, (4, 1), 360),
    Case("two_coupled_tips", 2, True, (2, 0), 120),
)


def canonical(colors: tuple[int, ...]) -> str:
    """Rename colors by first occurrence, preserving only equality patterns."""
    names: dict[int, int] = {}
    return "".join(str(names.setdefault(color, len(names))) for color in colors)


def falling_factorial(n: int, r: int) -> int:
    result = 1
    for j in range(r):
        result *= n - j
    return result


def require(checks: dict[str, bool], name: str, condition: bool) -> None:
    checks[name] = bool(condition)
    if not condition:
        raise RuntimeError(f"Failed verification: {name}")


def graph(case: Case) -> tuple[tuple[str, ...], tuple[tuple[int, int], ...]]:
    vertices = PORTS + ("x", "y")[: case.tip_count]
    edges = list(SKELETON_EDGES)
    for tip in range(4, len(vertices)):
        edges.extend((port, tip) for port in range(4))
    if case.coupled:
        if case.tip_count != 2:
            raise ValueError("A coupled case requires exactly two tips")
        edges.append((4, 5))
    return vertices, tuple(edges)


def expected_extension_formula(case: Case, used_colors: int) -> tuple[int, str]:
    """Count choices from unused colors, independently of graph enumeration."""
    available = K - used_colors
    if case.coupled:
        return available * (available - 1), "(5-d)*(5-d-1)"
    return available ** case.tip_count, f"(5-d)^{case.tip_count}"


def enumerate_case(case: Case) -> tuple[dict, dict[tuple[int, ...], int]]:
    vertices, edges = graph(case)
    boundary_counts = dict.fromkeys(product(range(K), repeat=len(PORTS)), 0)
    examined = 0
    proper = 0
    for coloring in product(range(K), repeat=len(vertices)):
        examined += 1
        if all(coloring[u] != coloring[v] for u, v in edges):
            proper += 1
            boundary_counts[coloring[: len(PORTS)]] += 1

    orbit_sizes: Counter[str] = Counter()
    orbit_counts: dict[str, set[int]] = defaultdict(set)
    skeleton_counts: dict[str, set[int]] = defaultdict(set)
    invalid_skeleton_have_zero_extensions = True
    for boundary, extensions in boundary_counts.items():
        state = canonical(boundary)
        orbit_sizes[state] += 1
        orbit_counts[state].add(extensions)
        if all(boundary[u] != boundary[v] for u, v in SKELETON_EDGES):
            skeleton_counts[state].add(extensions)
        else:
            invalid_skeleton_have_zero_extensions &= extensions == 0

    checks: dict[str, bool] = {}
    require(checks, "visited_all_labeled_assignments", examined == K ** len(vertices))
    require(checks, "all_boundary_assignments_accounted_for", len(boundary_counts) == K ** len(PORTS))
    require(checks, "color_renaming_preserves_extension_count", all(len(counts) == 1 for counts in orbit_counts.values()))
    require(checks, "skeleton_boundary_language", tuple(sorted(skeleton_counts)) == SKELETON_RELATION)
    require(checks, "invalid_skeleton_boundaries_have_no_extensions", invalid_skeleton_have_zero_extensions)

    complete_extension_counts = {state: next(iter(orbit_counts[state])) for state in sorted(orbit_counts)}
    relation = [state for state, count in complete_extension_counts.items() if count > 0]
    expected_by_state = dict(zip(SKELETON_RELATION, case.expected_extensions))
    actual_by_state = {state: complete_extension_counts[state] for state in SKELETON_RELATION}
    require(checks, "fixed_boundary_extension_counts_match_expected", actual_by_state == expected_by_state)
    require(checks, "canonical_port_relation_matches_expected", relation == [state for state in SKELETON_RELATION if expected_by_state[state] > 0])

    formula_rows = []
    analytic_total = 0
    for state in SKELETON_RELATION:
        d = len(set(state))
        analytic_extensions, formula = expected_extension_formula(case, d)
        labelings = falling_factorial(K, d)
        analytic_total += labelings * analytic_extensions
        require(checks, f"formula_matches_extensions_{state}", analytic_extensions == actual_by_state[state])
        require(checks, f"color_orbit_size_matches_falling_factorial_{state}", orbit_sizes[state] == labelings)
        formula_rows.append({
            "canonical_boundary": state,
            "used_colors_d": d,
            "unused_colors": K - d,
            "labeled_boundary_count": labelings,
            "labeled_boundary_count_formula": f"(5)_{d}",
            "extensions_per_fixed_labeled_boundary": actual_by_state[state],
            "analytic_extension_formula": formula,
            "analytic_extension_count": analytic_extensions,
            "contribution_to_proper_total": labelings * analytic_extensions,
        })

    require(checks, "proper_total_equals_sum_over_raw_boundaries", proper == sum(boundary_counts.values()))
    require(checks, "proper_total_matches_analytic_formula", proper == analytic_total)
    require(checks, "proper_total_matches_fixed_expected_value", proper == case.expected_proper_total)

    report = {
        "case": case.name,
        "vertices": list(vertices),
        "ports_in_order": list(PORTS),
        "edges": [[vertices[u], vertices[v]] for u, v in edges],
        "vertex_count": len(vertices),
        "edge_count": len(edges),
        "tip_count": case.tip_count,
        "tips_coupled_by_an_edge": case.coupled,
        "total_labeled_assignments_examined": examined,
        "expected_assignments_examined": K ** len(vertices),
        "total_assignment_formula": f"5^{len(vertices)}",
        "proper_labeled_colorings": proper,
        "rejected_labeled_assignments": examined - proper,
        "canonical_port_relation": relation,
        "skeleton_boundary_extension_counts": actual_by_state,
        "all_canonical_boundary_extension_counts": complete_extension_counts,
        "extension_count_convention": (
            "Counts are internal extensions of one fixed labeled boundary assignment. "
            "Every relabeling in each canonical boundary class was enumerated and "
            "checked to have the same count. Zero-extension boundary classes are retained."
        ),
        "analytic_count_rows": formula_rows,
        "analytic_total_formula": (
            f"60*{actual_by_state['0122']} + 120*{actual_by_state['0123']}"
        ),
        "analytic_proper_total": analytic_total,
        "expected_proper_total": case.expected_proper_total,
        "checks": checks,
        "all_checks_passed": all(checks.values()),
    }
    return report, boundary_counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True, help="Directory for transparent_gluing_results.json")
    args = parser.parse_args()

    results = []
    raw_counts = {}
    for case in CASES:
        result, counts = enumerate_case(case)
        results.append(result)
        raw_counts[case.name] = counts

    checks: dict[str, bool] = {}
    baseline = raw_counts["k4_minus_edge"]
    one = raw_counts["one_tip"]
    two = raw_counts["two_uncoupled_tips"]
    coupled = raw_counts["two_coupled_tips"]
    require(checks, "one_tip_preserves_every_labeled_boundary_feasibility", all((baseline[b] > 0) == (one[b] > 0) for b in baseline))
    require(checks, "two_uncoupled_tips_preserve_every_labeled_boundary_feasibility", all((baseline[b] > 0) == (two[b] > 0) for b in baseline))
    require(checks, "independent_internal_extension_counts_multiply", all(two[b] == one[b] * one[b] for b in baseline))
    require(checks, "coupled_negative_control_removes_exactly_four_color_boundaries", all((coupled[b] > 0) == (baseline[b] > 0 and len(set(b)) == 3) for b in baseline))

    # This naming map is only an abstract correspondence to the upstream outer
    # language, not evidence that its large graph has the same relation.
    expanded = []
    for state in SKELETON_RELATION:
        a, b, c, d = map(int, state)
        expanded.append(canonical((b, a, c, c, b, d)))
    require(checks, "abstract_six_position_renaming", expanded == ["012202", "012203"])

    total_examined = sum(result["total_labeled_assignments_examined"] for result in results)
    require(checks, "total_enumeration_size", total_examined == 35000)
    all_passed = all(result["all_checks_passed"] for result in results) and all(checks.values())
    report = {
        "status": "ABSTRACT-TRANSPARENT-GLUING-VERIFIED",
        "colors": list(range(K)),
        "method": "Complete labeled assignment enumeration with itertools.product; no pruning, SAT solver, or third-party package.",
        "scope": (
            "Four explicit abstract finite graphs and their proper 5-coloring relations. "
            "This is a separate control experiment, not verification of the upstream "
            "conditional quotient/P2 SAT leaves. No planar unit-distance realization, "
            "Hadwiger--Nelson bound, or P-versus-NP result is claimed."
        ),
        "boundary_relation_definition": "A boundary coloring belongs to R_G(S) iff it extends to a proper 5-coloring of all of G.",
        "transparent_gluing_condition": {
            "shared_vertices": list(PORTS),
            "shared_terminal_skeleton": "K4 minus C--D",
            "internal_vertices_disjoint": True,
            "cross_edges_between_internals": False,
            "identity": "R_(G1 union_S G2)(S) = R_G1(S) intersection R_G2(S)",
            "count_identity": "For each fixed labeled boundary, independent internal extension counts multiply.",
            "negative_control": "The x--y edge violates internal independence and removes boundary state 0123.",
        },
        "proof_explanation": [
            "The skeleton forces A,B,C pairwise different and D different from A,B, giving 0122 or 0123.",
            "A universal tip can use any of the 5-d colors absent from its four terminal neighbors.",
            "Independent tips can reuse their colors: two tips give (5-d)^2 extensions.",
            "Coupled tips must differ: two coupled tips give (5-d)*(5-d-1) extensions.",
            "Thus both uncoupled cases preserve feasibility, while coupling removes exactly the d=4 state.",
        ],
        "abstract_outer_naming_correspondence": {
            "expanded_order": ["B", "A", "C", "C", "B", "D"],
            "canonical_states": expanded,
            "scope": "A renaming identity for this toy skeleton only; not a verification of any upstream graph or solver leaf.",
        },
        "cases": results,
        "cross_case_checks": checks,
        "total_assignments_examined": total_examined,
        "all_checks_passed": all_passed,
    }
    args.out_dir.mkdir(parents=True, exist_ok=True)
    output_path = args.out_dir / "transparent_gluing_results.json"
    output_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": report["status"],
        "all_checks_passed": all_passed,
        "total_assignments_examined": total_examined,
        "cases": [
            {key: result[key] for key in (
                "case", "canonical_port_relation", "skeleton_boundary_extension_counts",
                "proper_labeled_colorings", "total_labeled_assignments_examined",
            )}
            for result in results
        ],
        "output": str(output_path.resolve()),
    }, indent=2))


if __name__ == "__main__":
    main()
