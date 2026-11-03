#!/usr/bin/env python3
"""Exact finite SAT-to-stationarity experiment; Python standard library only.

For a CNF F on n bits, define the compactly described deterministic map

    T_F(x) = x                     if F(x) is true,
             (x + 1) mod 2**n      otherwise.

One map evaluation checks F and increments an n-bit assignment.  This program
ALSO explicitly enumerates all 2**n transitions for finite verification.  Those
are distinct operations: the latter incurs exponential time/storage in n.

The deterministic point x is not the same object as a probability distribution
mu over assignments.  A directed cycle has a uniform stationary distribution,
even if none of its individual states is fixed.  For this particular map:
  * if F is satisfiable, every recurrent class is a satisfying absorbing state;
  * if F is unsatisfiable, the entire assignment space is one directed cycle.

The experiment illustrates where resources go when one asks for stationary
states.  It is NOT a polynomial-time SAT solver, a SAT lower bound, a physical
CTC implementation, or a reproduction of the bosonic model in the source repo.
All three CNF families here are easy.  An exponential walk on an easy family
only establishes a property of this deliberately simple walk.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter, deque
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import time


CNF = tuple[tuple[int, ...], ...]
PROVENANCE = {
    "theory": {
        "title": "Closed Timelike Curves Make Quantum and Classical Computing Equivalent",
        "authors": ["Scott Aaronson", "John Watrous"],
        "url": "https://arxiv.org/abs/0808.2669",
        "use": "Motivation for distinguishing an ideal fixed-point resource from ordinary simulation; this script does not implement the paper's full PSPACE construction.",
    },
    "existing_repository": {
        "url": "https://github.com/HeliCorgi/spacetime-screening",
        "commit": "f7a52ba2d25a3322ffd9ed250a265cc18853f105",
        "v7_code": "https://github.com/HeliCorgi/spacetime-screening/blob/f7a52ba2d25a3322ffd9ed250a265cc18853f105/src/numerical/sa_deutsch_fixed_point_v7.py",
        "v7_note": "https://github.com/HeliCorgi/spacetime-screening/blob/f7a52ba2d25a3322ffd9ed250a265cc18853f105/notes/sa-deutsch-fixed-point-v7.md",
        "use": "Transfer of the idea of explicitly checking a proposed fixed-point construction and its scope. No source code, Gaussian/Fock dynamics, or physics is imported.",
    },
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def satisfies(cnf: CNF, assignment: int) -> bool:
    """DIMACS literals: variable 1 is the least significant bit of assignment."""
    return all(
        any(bool((assignment >> (abs(literal) - 1)) & 1) == (literal > 0)
            for literal in clause)
        for clause in cnf
    )


def successor(cnf: CNF, assignment: int, mask: int) -> int:
    """One CNF evaluation plus, when needed, an n-bit increment."""
    return assignment if satisfies(cnf, assignment) else (assignment + 1) & mask


def families(n: int) -> dict[str, CNF]:
    require(n >= 2, "The many-solution example needs at least two variables.")
    return {
        "unique_all_ones": tuple((variable,) for variable in range(1, n + 1)),
        "unsat_contradiction": ((1,), (-1,)),
        "many_xor_first_two": ((1, 2), (-1, -2)),
    }


def direct_walk(cnf: CNF, n: int) -> dict:
    """Call the compact successor directly; do not use an enumerated table."""
    mask = (1 << n) - 1
    seen: dict[int, int] = {}
    prefix: list[int] = []
    tail: deque[int] = deque(maxlen=12)
    state = 0
    transitions = 0
    calls = 0
    started = time.perf_counter()
    while True:
        seen[state] = transitions
        if len(prefix) < 12:
            prefix.append(state)
        tail.append(state)
        next_state = successor(cnf, state, mask)
        calls += 1
        if next_state == state:
            return {
                "start": 0, "kind": "fixed_point", "fixed_state": state,
                "steps_to_fixed_point": transitions,
                "steps_to_first_repeat": None, "cycle_period": 1,
                "map_evaluations": calls,
                "distinct_visited_states": len(seen),
                "fixed_state_satisfies": satisfies(cnf, state),
                "prefix": prefix, "tail": list(tail),
                "seconds": time.perf_counter() - started,
                "counting_convention": "Steps exclude the final self-loop; the last map evaluation confirms absorption.",
            }
        transitions += 1
        if next_state in seen:
            return {
                "start": 0, "kind": "nontrivial_cycle", "fixed_state": None,
                "steps_to_fixed_point": None,
                "steps_to_first_repeat": transitions,
                "cycle_period": transitions - seen[next_state],
                "cycle_entry_step": seen[next_state],
                "map_evaluations": calls,
                "distinct_visited_states": len(seen),
                "prefix": prefix, "tail": list(tail),
                "first_repeated_state": next_state,
                "seconds": time.perf_counter() - started,
                "counting_convention": "Steps include the transition that first revisits a state.",
            }
        state = next_state


def recurrent_cycles(transitions: list[int]) -> list[list[int]]:
    """Find every directed cycle of a finite functional graph in linear time."""
    size = len(transitions)
    require(all(0 <= target < size for target in transitions), "Invalid transition.")
    status = [0] * size  # unseen, active in current path, completed
    position = [-1] * size
    cycles: list[list[int]] = []
    for start in range(size):
        if status[start] != 0:
            continue
        path: list[int] = []
        current = start
        while status[current] == 0:
            status[current] = 1
            position[current] = len(path)
            path.append(current)
            current = transitions[current]
        if status[current] == 1:
            cycle = path[position[current]:]
            first = cycle.index(min(cycle))
            cycles.append(cycle[first:] + cycle[:first])
        for state in path:
            status[state] = 2
            position[state] = -1
    return sorted(cycles, key=lambda cycle: cycle[0])


def recurrent_nodes_by_pruning(transitions: list[int]) -> set[int]:
    """Independent check: remove indegree-zero nodes until only cycles remain."""
    indegree = [0] * len(transitions)
    for target in transitions:
        indegree[target] += 1
    queue = deque(state for state, degree in enumerate(indegree) if degree == 0)
    while queue:
        state = queue.popleft()
        target = transitions[state]
        indegree[target] -= 1
        if indegree[target] == 0:
            queue.append(target)
    return {state for state, degree in enumerate(indegree) if degree > 0}


def basin_summary(transitions: list[int], cycles: list[list[int]]) -> dict:
    basin = [-1] * len(transitions)
    distance = [-1] * len(transitions)
    for index, cycle in enumerate(cycles):
        for state in cycle:
            basin[state] = index
            distance[state] = 0
    for start in range(len(transitions)):
        if basin[start] >= 0:
            continue
        path = []
        current = start
        while basin[current] < 0:
            path.append(current)
            current = transitions[current]
        for state in reversed(path):
            basin[state] = basin[current]
            distance[state] = distance[current] + 1
            current = state
    counts = Counter(basin)
    return {
        "max_steps_to_recurrence": max(distance),
        "basin_size_histogram": dict(sorted(Counter(counts.values()).items())),
    }


def analyze_case(family: str, cnf: CNF, n: int) -> dict:
    size = 1 << n
    walk = direct_walk(cnf, n)
    started = time.perf_counter()
    truth = [satisfies(cnf, state) for state in range(size)]
    transitions = [state if truth[state] else (state + 1) % size for state in range(size)]
    enumeration_seconds = time.perf_counter() - started

    started = time.perf_counter()
    cycles = recurrent_cycles(transitions)
    recurrent = {state for cycle in cycles for state in cycle}
    require(recurrent == recurrent_nodes_by_pruning(transitions),
            "Cycle analysis disagrees with independent indegree pruning.")
    # On each directed cycle, the pushforward of uniform mass must be exactly
    # uniform. Integer incoming counts avoid any floating-point tolerance.
    for cycle in cycles:
        require(Counter(transitions[state] for state in cycle) == Counter(cycle),
                "A claimed uniform cycle measure is not stationary.")
    stationary_sat_expectations = sorted({
        Fraction(sum(truth[state] for state in cycle), len(cycle)) for cycle in cycles
    })
    satisfying_count = sum(truth)
    fixed_count = sum(state == target for state, target in enumerate(transitions))
    require(fixed_count == satisfying_count, "Fixed states must equal satisfying assignments.")
    if satisfying_count:
        require(all(len(cycle) == 1 and truth[cycle[0]] for cycle in cycles),
                "A satisfiable case has a nonsatisfying recurrent class.")
        require(stationary_sat_expectations == [Fraction(1)],
                "Not every stationary extreme point accepts.")
    else:
        require(len(cycles) == 1 and len(cycles[0]) == size,
                "An unsatisfiable case must form one cycle over all assignments.")
        require(stationary_sat_expectations == [Fraction(0)],
                "An unsatisfiable stationary state must reject.")

    if family == "unique_all_ones":
        require(satisfying_count == 1 and cycles == [[size - 1]], "Unique-family check failed.")
        require(walk["steps_to_fixed_point"] == size - 1, "Unique-family walk length failed.")
    elif family == "unsat_contradiction":
        require(satisfying_count == 0 and walk["cycle_period"] == size,
                "Contradiction-family check failed.")
    elif family == "many_xor_first_two":
        require(satisfying_count == size // 2 and len(cycles) == size // 2,
                "XOR-family count disagrees with the independent half-space count.")
        require(walk["steps_to_fixed_point"] == 1 and walk["fixed_state"] == 1,
                "XOR-family walk check failed.")
    else:
        raise ValueError(f"Unknown experiment family: {family}")

    basins = basin_summary(transitions, cycles)
    analysis_seconds = time.perf_counter() - started
    return {
        "family": family, "n": n, "num_assignments": size,
        "cnf_dimacs_literals": [list(clause) for clause in cnf],
        "num_clauses": len(cnf), "num_literals": sum(map(len, cnf)),
        "satisfying_assignments": satisfying_count,
        "single_state_fixed_points": fixed_count,
        "recurrent_classes": len(cycles),
        "recurrent_states": len(recurrent), "transient_states": size - len(recurrent),
        "cycle_length_histogram": dict(sorted(Counter(map(len, cycles)).items())),
        **basins,
        "stationarity": {
            "definition": "mu(y) = sum_{x:T_F(x)=y} mu(x)",
            "all_extreme_stationary_distributions_checked_exactly": True,
            "check_method": "Integer incoming counts verify uniform mass on every recurrent cycle; independent indegree pruning confirms the complete recurrent-node set.",
            "finite_graph_fact_used": "Every stationary distribution of a finite deterministic transition system is a convex combination of uniform measures on its directed cycles; transient nodes have zero stationary mass.",
            "satisfiability_expectations_at_all_extreme_points": [str(value) for value in stationary_sat_expectations],
            "all_stationary_distributions_supported_on_satisfying_states":
                bool(satisfying_count) and all(truth[state] for state in recurrent),
            "classification": (
                "Convex combinations of point masses at satisfying assignments."
                if satisfying_count else
                "Unique uniform stationary distribution on the full assignment cycle; no single-state fixed point."
            ),
            "sample_extreme_distributions": [
                {"cycle_representative": cycle[0], "cycle_length": len(cycle),
                 "first_cycle_states": cycle[:12],
                 "mass_at_each_cycle_state": str(Fraction(1, len(cycle))),
                 "satisfiability_expectation": str(Fraction(sum(truth[state] for state in cycle), len(cycle)))}
                for cycle in cycles[:4]
            ],
            "samples_only_note": "The displayed examples are truncated; the counts and exact checks cover every recurrent class.",
        },
        "direct_compact_map_walk_from_zero": walk,
        "explicit_transition_table": {
            "enumerated": True, "entries": size,
            "formula_evaluations": size,
            "theoretical_fixed_width_target_bits": size * n,
            "memory_note": "This is only the target array's packed n-bit lower-level representation size, not measured Python memory; Python objects and analysis arrays use more.",
            "seconds": enumeration_seconds,
            "scope": "Exponential finite enumeration, separate from the compact formula and from one successor evaluation.",
        },
        "analysis_seconds": analysis_seconds,
        "checked": True,
    }


def self_check() -> dict:
    # A graph with two nontrivial cycles, an absorbing state, and a transient
    # checks that graph analysis does not assume the special SAT-map structure.
    graph = [1, 2, 1, 4, 3, 5]
    require(recurrent_cycles(graph) == [[1, 2], [3, 4], [5]],
            "Mixed functional graph cycle test failed.")
    require(recurrent_nodes_by_pruning(graph) == {1, 2, 3, 4, 5},
            "Mixed functional graph pruning test failed.")
    require(basin_summary(graph, recurrent_cycles(graph))["max_steps_to_recurrence"] == 1,
            "Mixed functional graph basin test failed.")
    # Hand-written two-bit truth tables separately check the literal convention.
    expected = {
        "unique_all_ones": [False, False, False, True],
        "unsat_contradiction": [False, False, False, False],
        "many_xor_first_two": [False, True, True, False],
    }
    for family, cnf in families(2).items():
        require([satisfies(cnf, state) for state in range(4)] == expected[family],
                f"Hand-written truth table failed for {family}.")
    return {"passed": True, "checks": ["Mixed functional graph with two cycles, one absorber, and a transient", "Hand-written two-bit truth tables for all three families", "Every reported case additionally checks analytic family counts, cycle measures, and independent pruning"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=[4, 8, 12, 16])
    args = parser.parse_args()
    require(all(2 <= n <= 20 for n in args.sizes),
            "Use 2 <= n <= 20: this program intentionally materializes 2**n transitions.")
    sizes = sorted(set(args.sizes))
    checks = self_check()
    cases = [analyze_case(family, cnf, n) for n in sizes for family, cnf in families(n).items()]
    payload = {
        "format_version": 1,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "experiment": "SAT-to-stationarity via hold-or-increment maps",
        "environment": {"python": platform.python_version(), "implementation": platform.python_implementation(), "dependencies": "Python standard library only"},
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "provenance": PROVENANCE,
        "map_definition": "T_F(x)=x when F(x)=true; otherwise T_F(x)=(x+1) mod 2**n.",
        "compact_map_cost": "One CNF evaluation plus an n-bit increment; polynomial in the encoded formula and assignment lengths. Python integers and random bit access are not treated as unit-cost unbounded arithmetic.",
        "important_distinctions": [
            "A single-state fixed point and a stationary probability distribution are different objects.",
            "Compact map description and one map evaluation do not enumerate the exponentially many states.",
            "This program explicitly enumerates all transitions to verify each finite instance, so it pays exponential time and memory.",
            "The unsatisfiable walk cycles forever from a point state. An invariant uniform distribution exists without the walk converging to it.",
            "The three chosen formula families are easy. The unique-family 2**n-1 walk proves no lower bound for SAT or for other algorithms.",
            "Ideal fixed-point selection is an added computational resource. Neither physical CTCs nor a polynomial-time classical fixed-point solver are implemented.",
            "This is a new finite classical experiment, not a direct insertion of SAT into the reference repository's Gaussian/Fock toy model.",
            "Wall times are single-run diagnostics, not asymptotic evidence or controlled performance benchmarks.",
        ],
        "self_checks": checks,
        "cases": cases,
    }
    args.out_dir.mkdir(parents=True, exist_ok=True)
    json_path = args.out_dir / "fixedpoint_sat_results.json"
    csv_path = args.out_dir / "fixedpoint_sat_summary.csv"
    json_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    fields = ["family", "n", "num_assignments", "satisfying_assignments", "single_state_fixed_points", "recurrent_classes", "max_steps_to_recurrence", "walk_kind", "steps_to_fixed_point", "steps_to_first_repeat", "map_evaluations", "stationary_sat_expectation", "enumerated_transition_entries", "walk_seconds", "enumeration_seconds", "analysis_seconds"]
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        for case in cases:
            walk = case["direct_compact_map_walk_from_zero"]
            row = {key: case[key] for key in fields if key in case}
            row.update({
                "walk_kind": walk["kind"],
                "steps_to_fixed_point": walk["steps_to_fixed_point"],
                "steps_to_first_repeat": walk["steps_to_first_repeat"],
                "map_evaluations": walk["map_evaluations"],
                "stationary_sat_expectation": ";".join(case["stationarity"]["satisfiability_expectations_at_all_extreme_points"]),
                "enumerated_transition_entries": case["explicit_transition_table"]["entries"],
                "walk_seconds": walk["seconds"],
                "enumeration_seconds": case["explicit_transition_table"]["seconds"],
            })
            writer.writerow(row)
    print(json.dumps({
        "passed": True, "cases": len(cases), "sizes": sizes,
        "unique_walk_steps": {str(case["n"]): case["direct_compact_map_walk_from_zero"]["steps_to_fixed_point"] for case in cases if case["family"] == "unique_all_ones"},
        "unsat_cycle_lengths": {str(case["n"]): case["direct_compact_map_walk_from_zero"]["cycle_period"] for case in cases if case["family"] == "unsat_contradiction"},
        "many_absorbing_states": {str(case["n"]): case["single_state_fixed_points"] for case in cases if case["family"] == "many_xor_first_two"},
        "json": str(json_path.resolve()), "csv": str(csv_path.resolve()),
        "scope": "Finite exact graph checks only. These easy families and this slow walk establish no SAT lower bound and implement no physical CTC.",
    }, ensure_ascii=False))


if __name__ == "__main__":
    main()
