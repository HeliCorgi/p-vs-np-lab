#!/usr/bin/env python3
"""Independently reconstruct a small saved HN boundary relation.

Input: a solver-derived *saved* 12-state relation. This program does not
re-solve its source graph or certify its geometry. It does independently
enumerate the complete seven-port partition universe, derive all common
pairwise facts, and exhaust the two-literal clause-cover problem.

All work uses Python's standard library and exact finite logic.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE_PATH = "results/separator-left-q8-q9-relation-cnf/analysis.json"
Literal = tuple[int, int, bool]  # positions i,j; True means equality


def partitions(width: int, colors: int = 5):
    """Canonical set partitions, with fixed ordered ports and unnamed colors."""
    if width == 0:
        yield ()
        return

    def visit(prefix, highest):
        if len(prefix) == width:
            yield tuple(prefix)
            return
        for color in range(min(highest + 1, colors - 1) + 1):
            yield from visit(prefix + [color], max(highest, color))

    yield from visit([0], 0)


def state_key(state):
    return "".join(map(str, state))


def holds(state, literal: Literal):
    i, j, equal = literal
    return (state[i] == state[j]) == equal


def describe_literal(literal, ports):
    i, j, equal = literal
    return {"qnodes": [ports[i], ports[j]], "kind": "eq" if equal else "neq"}


def partition_count(width: int, colors: int = 5):
    """Stirling recurrence, without materializing the partition universe."""
    counts = [1] + [0] * colors
    for _ in range(width):
        counts = [0] + [j * counts[j] + counts[j - 1] for j in range(1, colors + 1)]
    return sum(counts)


def analyze(out_dir: Path):
    manifest_path = ROOT / "upstream" / "SOURCE_MANIFEST.json"
    manifest = json.loads(manifest_path.read_text())
    record = next(x for x in manifest["files"] if x["path"] == SOURCE_PATH)
    source = ROOT / "upstream" / "hadwiger-nelson-lab" / SOURCE_PATH
    data = source.read_bytes()
    assert hashlib.sha256(data).hexdigest() == record["sha256"]
    saved = json.loads(data)
    ports = saved["separator_qnodes"]
    target = {tuple(map(int, s)) for s in saved["large_side_states"]}
    universe = list(partitions(len(ports)))
    assert len(universe) == partition_count(len(ports))
    assert target <= set(universe)

    # Derive the common facts from target states; do not trust saved facts.
    atoms = [(i, j, eq) for i, j in itertools.combinations(range(len(ports)), 2)
             for eq in (True, False)]
    common = [a for a in atoms if all(holds(s, a) for s in target)]
    baseline = {s for s in universe if all(holds(s, a) for a in common)}
    extras = sorted(baseline - target)

    # All unordered pairs of distinct equality/disequality literals are tried.
    # Valid unary literals were already incorporated into common facts.
    candidates = []
    raw_pair_count = 0
    for clause in itertools.combinations(atoms, 2):
        raw_pair_count += 1
        if not all(any(holds(s, a) for a in clause) for s in target):
            continue
        excluded = [i for i, s in enumerate(extras)
                    if not any(holds(s, a) for a in clause)]
        if not excluded:
            continue
        candidates.append({"clause": clause, "mask": sum(1 << i for i in excluded),
                           "eliminates": [state_key(extras[i]) for i in excluded]})

    full_mask = (1 << len(extras)) - 1
    exhaustive_cover_checks = []
    minimum_covers = []
    for size in range(len(candidates) + 1):
        tried = 0
        solutions = []
        for indices in itertools.combinations(range(len(candidates)), size):
            tried += 1
            covered = 0
            for i in indices:
                covered |= candidates[i]["mask"]
            if covered == full_mask:
                solutions.append(indices)
        exhaustive_cover_checks.append({"size": size, "subsets_checked": tried,
                                        "cover_count": len(solutions)})
        if solutions:
            minimum_covers = solutions
            break
    assert minimum_covers
    selected = minimum_covers[0]
    accepted = {s for s in universe if all(holds(s, a) for a in common)
                and all(any(holds(s, a) for a in candidates[i]["clause"])
                        for i in selected)}
    assert accepted == target

    # Also compare against the repository's chosen formula, independently
    # evaluated on the complete universe. Saved verification flags are unused.
    positions = {v: i for i, v in enumerate(ports)}
    saved_clauses = [tuple((positions[a["qnodes"][0]], positions[a["qnodes"][1]],
                            a["kind"] == "eq") for a in c["literals"])
                     for c in saved["chosen_width2_clauses"]]
    saved_accepted = {s for s in universe if all(holds(s, a) for a in common)
                      and all(any(holds(s, a) for a in clause)
                              for clause in saved_clauses)}
    assert saved_accepted == target

    private_witnesses = []
    for removed in selected:
        remaining = [i for i in selected if i != removed]
        newly_allowed = [state_key(s) for s in extras
                         if all(any(holds(s, a) for a in candidates[i]["clause"])
                                for i in remaining)]
        private_witnesses.append({"removed_candidate": removed,
                                  "extra_states_become_allowed": newly_allowed})
        assert newly_allowed

    unique_excluder_witnesses = []
    for position, state in enumerate(extras):
        excluders = [i for i, candidate in enumerate(candidates)
                     if candidate["mask"] & (1 << position)]
        if len(excluders) == 1:
            unique_excluder_witnesses.append({
                "extra_state": state_key(state),
                "only_candidate_that_excludes_it": excluders[0],
            })

    boundary_counts = []
    for width in (0, 1, 4, 6, 7, 8, 10, 12, 16, 20):
        count = partition_count(width)
        if width:
            assert count == (5**width + 10 * 3**width + 20 * 2**width + 45) // 120
        boundary_counts.append({"ports": width, "named_color_assignments": 5**width,
                                "canonical_partitions_at_most_5_colors": count})

    result = {
        "status": "PASS",
        "source_repository": manifest["repository"],
        "source_commit": manifest["commit"],
        "source_url": record["source_url"],
        "source_sha256": record["sha256"],
        "source_table_historical_upstream_sha": saved.get("upstream_sha"),
        "ports": ports,
        "canonical_universe_count": len(universe),
        "target_state_count": len(target),
        "target_states": sorted(map(state_key, target)),
        "derived_common_pairwise_fact_count": len(common),
        "derived_common_pairwise_facts": [describe_literal(a, ports) for a in common],
        "pairwise_only_state_count": len(baseline),
        "pairwise_only_extra_states": list(map(state_key, extras)),
        "two_literal_syntactic_candidates_considered": raw_pair_count,
        "valid_nontrivial_two_literal_clause_count": len(candidates),
        "candidate_clauses": [
            {"index": i, "literals": [describe_literal(a, ports) for a in c["clause"]],
             "eliminates_states": c["eliminates"]} for i, c in enumerate(candidates)],
        "exhaustive_cover_checks": exhaustive_cover_checks,
        "minimum_clause_count": len(minimum_covers[0]),
        "minimum_syntactic_cover_count": len(minimum_covers),
        "minimum_covers": minimum_covers,
        "selected_clause_necessity_witnesses": private_witnesses,
        "unique_excluder_witnesses_among_all_valid_candidates": unique_excluder_witnesses,
        "all_855_states_rechecked": len(universe) == 855 and accepted == target,
        "saved_formula_language_matches": saved_accepted == target,
        "boundary_counts": boundary_counts,
        "claim_scope": (
            "Minimum number of additional clauses after all pairwise consequences are fixed; "
            "each clause is an OR of at most two equality/disequality atoms on distinct port pairs. "
            "Not a minimum over arbitrary Boolean representations or algorithms."
        ),
        "trust_boundary": (
            "The 12-state target table is imported solver-derived data. This run independently "
            "verifies its finite representation and minimum cover, but does not re-solve the "
            "large source graph, certify geometric realizability, or establish a new HN bound."
        ),
        "complexity_scope": (
            "Boundary counts describe explicit enumeration before terminal constraints, "
            "not a lower bound for compressed representations or general SAT algorithms. "
            "Equality atoms are not independent Boolean variables, so two-literal clauses "
            "here do not by themselves make the problem ordinary 2-SAT."
        ),
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "boundary_compression.json").write_text(json.dumps(result, indent=2) + "\n")
    with (out_dir / "boundary_counts.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(boundary_counts[0]))
        writer.writeheader()
        writer.writerows(boundary_counts)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    result = analyze(args.out_dir)
    print(json.dumps({k: result[k] for k in (
        "status", "canonical_universe_count", "target_state_count",
        "derived_common_pairwise_fact_count", "pairwise_only_state_count",
        "two_literal_syntactic_candidates_considered",
        "valid_nontrivial_two_literal_clause_count", "minimum_clause_count",
        "minimum_syntactic_cover_count", "exhaustive_cover_checks")}, indent=2))


if __name__ == "__main__":
    main()
