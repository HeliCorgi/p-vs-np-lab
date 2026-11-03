#!/usr/bin/env python3
"""Reproduce a known CNF representation barrier under existential projection.

A chain of n-1 XOR gates, encoded with four clauses per gate and one output
pin, has O(n) clauses of width at most three.  After its auxiliary variables
are existentially removed, its boundary relation is even parity.  An ordinary
CNF on those n boundary variables alone needs exactly 2**(n-1) clauses.

This is a known representation lower bound, not a P-versus-NP result.  Parity
has an O(n)-node OBDD and can be evaluated by a linear scan.  The finite checks
here deliberately enumerate boundary assignments and the exponential CNF.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
from typing import Iterable


Clause = tuple[int, ...]
CNF = tuple[Clause, ...]
FALSE_TERMINAL = -1
TRUE_TERMINAL = -2
SOURCES = [
    {
        "authors": ["Gregory Emdin", "Alexander S. Kulikov", "Ivan Mihajlin", "Nikita Slezkin"],
        "title": "CNF Encodings of Parity",
        "year": 2022,
        "url": "https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2022.47",
        "doi": "10.4230/LIPIcs.MFCS.2022.47",
        "used_for": "Known exact 2^(n-1) clause bound for CNF without auxiliary variables; distinction from encodings that retain auxiliaries.",
    },
    {
        "authors": ["Adnan Darwiche", "Pierre Marquis"],
        "title": "A Knowledge Compilation Map",
        "year": 2002,
        "url": "https://www.cs.cmu.edu/afs/cs.cmu.edu/project/jair/pub/volume17/darwiche02a.pdf",
        "used_for": "Representation-language comparisons; parity admits linear-size OBDDs but needs exponential-size flat CNF/DNF. Appendix discussion of Table 10.",
    },
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def clause_holds(clause: Clause, assignment: int) -> bool:
    """DIMACS literals; variable 1 is the least significant assignment bit."""
    return any(bool((assignment >> (abs(literal) - 1)) & 1) == (literal > 0)
               for literal in clause)


def cnf_holds(cnf: CNF, assignment: int) -> bool:
    return all(clause_holds(clause, assignment) for clause in cnf)


def xor_gate_clauses(a: int, b: int, output: int) -> CNF:
    """An exact Boolean equivalence output <-> (a XOR b), not a one-way gate."""
    if len({a, b, output}) != 3 or min(a, b, output) < 1:
        raise ValueError("XOR gate variables must be distinct positive identifiers.")
    return ((a, b, -output), (a, -b, output),
            (-a, b, output), (-a, -b, -output))


def xor_chain_cnf(n: int) -> CNF:
    """Variables 1..n are the boundary; n+1..2n-1 are prefix-parity outputs."""
    if n < 2:
        raise ValueError("At least two boundary variables are required.")
    clauses: list[Clause] = []
    previous = 1
    for boundary_variable in range(2, n + 1):
        output = n + boundary_variable - 1
        clauses.extend(xor_gate_clauses(previous, boundary_variable, output))
        previous = output
    clauses.append((-previous,))  # Require total parity zero.
    return tuple(clauses)


def induced_extension(n: int, boundary: int) -> int:
    """Compute the unique auxiliary assignment imposed by the feedforward gates."""
    if not 0 <= boundary < 1 << n:
        raise ValueError("Boundary assignment is out of range.")
    full = boundary
    prefix_parity = boundary & 1
    for boundary_bit in range(1, n):
        prefix_parity ^= (boundary >> boundary_bit) & 1
        full |= prefix_parity << (n + boundary_bit - 1)
    return full


def brute_projection_counts(cnf: CNF, n: int, auxiliary_count: int) -> tuple[int, ...]:
    """Independent small-instance oracle: enumerate every full assignment.

    This intentionally does not use prefix parity or induced_extension.
    """
    counts = [0] * (1 << n)
    boundary_mask = (1 << n) - 1
    for full in range(1 << (n + auxiliary_count)):
        if cnf_holds(cnf, full):
            counts[full & boundary_mask] += 1
    return tuple(counts)


def boundary_prime_cnf(n: int) -> CNF:
    """One full-width clause forbids each odd assignment, and no even one."""
    return tuple(
        tuple(-variable if (assignment >> (variable - 1)) & 1 else variable
              for variable in range(1, n + 1))
        for assignment in range(1 << n) if assignment.bit_count() % 2 == 1
    )


def cnf_truth_mask(cnf: CNF, n: int) -> int:
    """Generic exact truth-table evaluation using Python integer bit sets.

    The bit set has 2**n positions.  Bit-parallel execution is an optimization
    of explicit exponential enumeration, not a unit-cost huge-integer claim.
    """
    count = 1 << n
    universe = (1 << count) - 1
    positive = tuple(sum(1 << assignment for assignment in range(count)
                         if (assignment >> bit) & 1) for bit in range(n))
    result = universe
    for clause in cnf:
        clause_mask = 0
        for literal in clause:
            if not 1 <= abs(literal) <= n:
                raise ValueError("Clause uses a variable outside the truth table.")
            variable_mask = positive[abs(literal) - 1]
            clause_mask |= variable_mask if literal > 0 else universe ^ variable_mask
        result &= clause_mask
    return result


def parity_obdd(n: int) -> tuple[tuple[int, int, int], ...]:
    """Build an ordinary OBDD, without complemented edges, for even parity.

    Each node is (variable, low_child, high_child).  Node 0 is the root.
    Children -1 and -2 denote false and true terminals.  Prefix parity is
    the only state: width <= 2 and exactly 2*n-1 reachable internal nodes.
    """
    if n < 1:
        raise ValueError("An OBDD needs at least one input variable.")
    keys = [(0, 0)] + [(level, parity) for level in range(1, n) for parity in (0, 1)]
    identifiers = {key: index for index, key in enumerate(keys)}
    nodes = []
    for level, parity in keys:
        children = []
        for bit in (0, 1):
            updated = parity ^ bit
            if level == n - 1:
                children.append(TRUE_TERMINAL if updated == 0 else FALSE_TERMINAL)
            else:
                children.append(identifiers[(level + 1, updated)])
        nodes.append((level + 1, children[0], children[1]))
    return tuple(nodes)


def obdd_holds(nodes: tuple[tuple[int, int, int], ...], assignment: int) -> bool:
    node = 0
    while node >= 0:
        variable, low, high = nodes[node]
        node = high if (assignment >> (variable - 1)) & 1 else low
    return node == TRUE_TERMINAL


def verify_gate_truth_table() -> None:
    gate = xor_gate_clauses(1, 2, 3)
    for a, b, output in itertools.product((0, 1), repeat=3):
        full = a | (b << 1) | (output << 2)
        require(cnf_holds(gate, full) == ((a ^ b) == output),
                "The gate CNF does not encode XOR equivalence.")


def verify_size(n: int, brute_max_n: int = 5) -> dict:
    """Verify one complete boundary relation and its two representations."""
    if not 2 <= n <= 14:
        raise ValueError("Use 2 <= n <= 14; boundary truth tables are explicit.")
    verify_gate_truth_table()
    count = 1 << n
    chain = xor_chain_cnf(n)
    prime = boundary_prime_cnf(n)
    obdd = parity_obdd(n)
    expected = tuple(assignment.bit_count() % 2 == 0 for assignment in range(count))
    projected = tuple(cnf_holds(chain, induced_extension(n, assignment))
                      for assignment in range(count))
    require(projected == expected, "The projected chain is not even parity.")
    expected_mask = sum(1 << assignment for assignment, accepted in enumerate(expected) if accepted)
    require(cnf_truth_mask(prime, n) == expected_mask,
            "The boundary CNF truth table differs from even parity.")
    require(tuple(obdd_holds(obdd, assignment) for assignment in range(count)) == expected,
            "The OBDD truth table differs from even parity.")
    require(len(chain) == 4 * (n - 1) + 1 and max(map(len, chain)) == 3,
            "Unexpected unsimplified chain size or width.")
    require(len(prime) == 1 << (n - 1), "Unexpected number of projected clauses.")
    require(len(obdd) == 2 * n - 1, "Unexpected OBDD size.")

    # Check every listed clause's unique forbidden assignment and every
    # single-literal deletion witness.  Flipping the deleted bit gives an even
    # assignment falsifying the shortened clause, certifying primality.
    falsifiers: set[int] = set()
    deletion_witnesses = 0
    for clause in prime:
        require({abs(literal) for literal in clause} == set(range(1, n + 1)),
                "A projected clause is not full width.")
        forbidden = sum(1 << (abs(literal) - 1) for literal in clause if literal < 0)
        require(forbidden.bit_count() % 2 == 1 and not clause_holds(clause, forbidden),
                "A clause does not forbid an odd assignment.")
        require(forbidden not in falsifiers, "Duplicate projected clause.")
        falsifiers.add(forbidden)
        for position, literal in enumerate(clause):
            witness = forbidden ^ (1 << (abs(literal) - 1))
            shortened = clause[:position] + clause[position + 1:]
            require(witness.bit_count() % 2 == 0 and not clause_holds(shortened, witness),
                    "A claimed prime clause has a redundant literal.")
            deletion_witnesses += 1
    require(falsifiers == {assignment for assignment in range(count) if not expected[assignment]},
            "The clauses do not cover precisely the odd assignments.")

    brute = None
    if n <= brute_max_n:
        brute = brute_projection_counts(chain, n, n - 1)
        require(brute == tuple(int(value) for value in expected),
                "Independent existential enumeration disagrees, including extension uniqueness.")

    return {
        "n": n,
        "boundary_variables": n,
        "auxiliary_variables": n - 1,
        "source_xor_gates": n - 1,
        "source_cnf_clauses": len(chain),
        "source_cnf_literal_occurrences": sum(map(len, chain)),
        "source_max_clause_width": 3,
        "source_size_convention": "Unsimplified four-clause XOR equivalences plus one unit output pin.",
        "boundary_assignments_enumerated": count,
        "accepted_boundary_assignments": sum(expected),
        "projected_cnf_clauses": len(prime),
        "projected_cnf_literal_occurrences": sum(map(len, prime)),
        "projected_max_clause_width": n,
        "known_minimum_boundary_only_cnf_clauses": 1 << (n - 1),
        "obdd_internal_nodes": len(obdd),
        "obdd_terminal_nodes": 2,
        "obdd_edges": 2 * len(obdd),
        "obdd_max_width": 2,
        "all_prime_clause_deletion_witnesses_checked": deletion_witnesses,
        "independent_auxiliary_bruteforce_performed": brute is not None,
        "independent_full_assignments_checked": (1 << (2 * n - 1)) if brute is not None else 0,
        "projection_check_method": "Truth-table-checked functional gates force a unique auxiliary extension; all boundary inputs are tested. Independent enumeration of all auxiliary choices is additionally used only for small n.",
        "truth_table_sha256": hashlib.sha256(bytes(expected)).hexdigest(),
        "sample_boundary_clauses": [list(clause) for clause in prime[:3]],
        "checks_passed": True,
    }


def run_experiment(sizes: Iterable[int] = range(3, 13), brute_max_n: int = 5) -> dict:
    """Return a deterministic JSON-serializable record; no clocks or host data."""
    selected = sorted(set(sizes))
    if not selected:
        raise ValueError("Choose at least one size.")
    if not 0 <= brute_max_n <= 8:
        raise ValueError("Keep independent full-assignment enumeration at n <= 8.")
    return {
        "schema_version": 1,
        "experiment": "parity_projection",
        "status": "verified",
        "claim_type": "Reproduction of a known elementary representation lower bound.",
        "relation": "R_n(x) = exists z: C_n(x,z) = [x_1 XOR ... XOR x_n = 0]",
        "source_size": "n-1 auxiliary variables; 4(n-1)+1 clauses; maximum width 3.",
        "lower_bound_scope": "Equivalent ordinary CNF over the boundary variables x only, with no auxiliaries or XOR operators: exactly 2^(n-1) clauses are necessary and sufficient.",
        "size_units": "Counts are variables, nodes, clauses, and literal occurrences. Explicit binary variable identifiers introduce logarithmic factors in a byte/bit encoding.",
        "meaning": "Small local constraints need not remain small when internal variables are eliminated into a fixed output grammar.",
        "not_claimed": [
            "A new parity lower bound or a solution of P versus NP.",
            "A lower bound for all algorithms, circuits, or representation languages.",
            "A barrier to retaining auxiliary variables or using native XOR constraints.",
            "A polynomial-time verification algorithm: finite truth tables and the projected prime CNF are explicitly enumerated.",
        ],
        "positive_control": "Even parity is computable by a linear scan and by the explicitly built width-two OBDD with 2n-1 internal nodes.",
        "sources": SOURCES,
        "cases": [verify_size(n, brute_max_n) for n in selected],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--sizes", nargs="+", type=int, default=list(range(3, 13)))
    parser.add_argument("--brute-max-n", type=int, default=5)
    args = parser.parse_args()
    payload = run_experiment(args.sizes, args.brute_max_n)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    destination = args.out_dir / "parity_projection.json"
    destination.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
                           encoding="utf-8")
    print(json.dumps({"status": "verified", "cases": len(payload["cases"]),
                      "output": str(destination),
                      "scope": payload["claim_type"]}, sort_keys=True))


if __name__ == "__main__":
    main()
