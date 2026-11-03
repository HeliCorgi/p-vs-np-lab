#!/usr/bin/env python3
"""Run the research experiments and compare their mathematical outputs.

Only Python's standard library is needed. Lean is a separate, explicit gate.
New reports are deterministic. Historical baseline comparisons discard only
timestamps, host information, and measured execution times, never counts,
formulas, witnesses, or pass/fail flags.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "experiments" / "baseline"
NEW_REPORTS = (
    "projection_barrier.json", "parity_projection.json", "affine_projection.json",
    "mixed_constraints.json", "three_sat_bridge.json",
    "parity_cuts.json",
    "joint_reasoning.json", "signature_counting.json", "upstream_parameters.json",
    "constant_block_bridge.json",
)
BASELINE_REPORTS = (
    "RUN_SUMMARY.json", "hn_existing_checker.json", "boundary_compression.json",
    "transparent-gluing/transparent_gluing_results.json",
    "fixedpoint/fixedpoint_sat_results.json",
)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
                    encoding="utf-8")


def verify_baseline_snapshot() -> int:
    """Check the entire migrated historical package, not just its SAT tables."""
    manifest = read_json(BASELINE / "PACKAGE_MANIFEST.json")
    for record in manifest["files"]:
        path = BASELINE / record["path"]
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != record["sha256"]:
            raise RuntimeError(f"Historical baseline file changed: {record['path']}")
    return len(manifest["files"])


def baseline_mathematics(value, filename: str):
    """Ignore an explicit, documented list of non-mathematical metadata."""
    ignored = set()
    if filename == "RUN_SUMMARY.json":
        ignored = {"python_version"}
    elif filename == "fixedpoint/fixedpoint_sat_results.json":
        ignored = {"created_at_utc", "environment", "seconds", "analysis_seconds"}

    def walk(item):
        if isinstance(item, dict):
            return {key: walk(val) for key, val in item.items() if key not in ignored}
        if isinstance(item, list):
            return [walk(val) for val in item]
        return item

    return walk(value)


def require_equal(actual, expected, description: str) -> None:
    if actual != expected:
        raise RuntimeError(f"Reproduction differs: {description}")


def run_component(script: Path, out: Path, log: Path) -> None:
    environment = dict(os.environ)
    environment["PYTHONPATH"] = str(ROOT / "src")
    process = subprocess.run(
        [sys.executable, str(script), "--out-dir", str(out)],
        cwd=ROOT, env=environment, capture_output=True, text=True,
    )
    log.write_text(process.stdout + process.stderr, encoding="utf-8")
    if process.returncode:
        raise RuntimeError(f"{script.name} failed; see {log}")
    print(f"PASS {script.relative_to(ROOT)}", flush=True)


def source_hashes() -> dict[str, str]:
    sources = set()
    for directory in ("src", "experiments", "tests", "scripts", "Formal"):
        sources.update(path for path in (ROOT / directory).rglob("*")
                       if path.suffix in {".py", ".lean"} and "__pycache__" not in path.parts)
    sources.update(ROOT / path for path in (
        "Formal.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain", "pyproject.toml",
        "experiments/baseline/PACKAGE_MANIFEST.json",
        "experiments/baseline/upstream/SOURCE_MANIFEST.json",
    ))
    sources.update((ROOT / "examples").glob("*.json"))
    sources.add(ROOT / "third_party/openai_math/manifest.json")
    manifest = read_json(ROOT / "third_party/openai_math/manifest.json")
    sources.update(ROOT / "third_party/openai_math" / item["path"] for item in manifest["files"])
    sources.update((ROOT / ".github/workflows").glob("*.yml"))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(sources)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "reproduced")
    parser.add_argument("--check", action="store_true",
                        help="Compare new deterministic reports with committed results/*.json.")
    args = parser.parse_args()
    out = args.out_dir.resolve()
    if args.check and out == (ROOT / "results").resolve():
        parser.error("--check requires an output directory different from results")
    out.mkdir(parents=True, exist_ok=True)

    snapshot_count = verify_baseline_snapshot()
    sys.path.insert(0, str(ROOT / "src"))
    sys.path.insert(0, str(ROOT))
    from scripts.verify_openai_math_snapshot import verify_snapshot
    math_snapshot = verify_snapshot()
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"))
    tests = unittest.TextTestRunner(verbosity=2).run(suite)
    if not tests.wasSuccessful() or not tests.testsRun:
        raise RuntimeError("Unit tests failed or no tests were discovered")

    for name in ("projection_barrier", "parity_projection", "affine_projection",
                 "mixed_constraints", "three_sat_bridge", "parity_cuts",
                 "joint_reasoning", "signature_counting", "upstream_parameters",
                 "constant_block_bridge"):
        run_component(ROOT / "experiments" / f"{name}.py", out, out / f"{name}.log")
    run_component(BASELINE / "run_all.py", out / "baseline", out / "baseline.log")

    for filename in BASELINE_REPORTS:
        require_equal(
            baseline_mathematics(read_json(out / "baseline" / filename), filename),
            baseline_mathematics(read_json(BASELINE / "results" / filename), filename),
            "historical baseline " + filename,
        )
    require_equal((out / "baseline/boundary_counts.csv").read_text(),
                  (BASELINE / "results/boundary_counts.csv").read_text(),
                  "historical boundary counts")

    star = read_json(out / NEW_REPORTS[0])
    parity = read_json(out / NEW_REPORTS[1])
    affine = read_json(out / NEW_REPORTS[2])
    mixed = read_json(out / NEW_REPORTS[3])
    bridge = read_json(out / NEW_REPORTS[4])
    cuts = read_json(out / NEW_REPORTS[5])
    joint = read_json(out / NEW_REPORTS[6])
    signatures = read_json(out / NEW_REPORTS[7])
    parameters = read_json(out / NEW_REPORTS[8])
    block_bridge = read_json(out / NEW_REPORTS[9])
    baseline = read_json(out / "baseline/RUN_SUMMARY.json")
    if (not star["all_checks_passed"]
            or not all(c["checks_passed"] for c in parity["cases"])
            or not all(c["checks_passed"] for c in affine["cases"])
            or not mixed["all_checks_passed"] or not bridge["all_checks_passed"]
            or not cuts["all_checks_passed"] or not joint["all_checks_passed"]
            or not signatures["all_checks_passed"] or not parameters["all_checks_passed"]
            or not block_bridge["all_checks_passed"]):
        raise RuntimeError("An experiment did not report success")

    summary = {
        "schema_version": 1,
        "status": "PASS",
        "unit_tests_passed": tests.testsRun,
        "historical_package_files_hash_verified": snapshot_count,
        "historical_reports_reproduced": len(BASELINE_REPORTS),
        "historical_result_scope": "Saved HN leaf tables remain trusted; no original SAT or geometry reproof.",
        "upstream_commit": baseline["upstream_commit"],
        "upstream_composition_checks": baseline["upstream_composition_checks"],
        "boundary_states_rechecked": baseline["boundary_states_rechecked"],
        "boundary_minimum_additional_clauses": baseline["boundary_minimum_additional_clauses"],
        "gluing_assignments_enumerated": baseline["gluing_assignments_enumerated"],
        "fixedpoint_cases": baseline["fixedpoint_cases"],
        "star_cases": len(star["cases"]),
        "star_widths": {str(c["q"]): c["minimum_required_clause_width"] for c in star["cases"]},
        "parity_cases": len(parity["cases"]),
        "parity_max_n": max(c["n"] for c in parity["cases"]),
        "affine_cases": len(affine["cases"]),
        "mixed_low_rank_cases": len(mixed["low_rank_cases"]),
        "mixed_enumeration_barrier_cases": len(mixed["enumeration_barrier_cases"]),
        "mixed_independent_oracle_cases": len(mixed["independent_oracle"]["cases"]),
        "mixed_original_assignments_checked": mixed["independent_oracle"]["full_original_assignments_checked"],
        "mixed_largest_barrier_cells": max(c["solver"]["checked_cells"] for c in mixed["enumeration_barrier_cases"]),
        "three_sat_bridge_checks_passed": bridge["all_checks_passed"],
        "parity_cut_checks_passed": cuts["all_checks_passed"],
        "parity_cut_independent_oracle_cases": cuts["summary"]["oracle_cases"],
        "parity_cut_original_assignments_checked": cuts["summary"]["oracle_original_assignments_checked"],
        "parity_cut_largest_zero_cell_exactly_one": cuts["summary"]["largest_exactly_one_variables"],
        "parity_cut_largest_full_hull_dimension_certified": cuts["summary"]["largest_full_hull_dimension_certified"],
        "parity_cut_algorithm_general_polynomial_time": False,
        "joint_checks_passed": joint["all_checks_passed"],
        "joint_summary": joint["summary"],
        "joint_algorithm_general_polynomial_time": False,
        "signature_counting_checks_passed": signatures["all_checks_passed"],
        "signature_counting_summary": signatures["summary"],
        "signature_algorithm_general_polynomial_time": False,
        "constant_block_bridge_checks_passed": block_bridge["all_checks_passed"],
        "constant_block_bridge_summary": block_bridge["summary"],
        "constant_block_bridge_general_polynomial_solver": False,
        "openai_math_snapshot": math_snapshot,
        "upstream_schedule_first_possible": parameters["first_possible"],
        "upstream_schedule_total_cutoff_computed": parameters["total_algorithm_cutoff_computed"],
        "upstream_proof_scope": "This command checks copied-source integrity and one finite parameter gate. It does not rebuild or certify the external ETH theorem; see the separate upstream audit record/workflow.",
        "mixed_algorithm_general_polynomial_time": False,
        "mixed_time_bound": "poly(N) + 2^r poly(N), where r is observed affine coefficient rank.",
        "lean_scope": "Not run by this Python command. Run lake build Formal; CI has a separate kernel-check job.",
        "p_vs_np": "No resolution or general algorithmic lower bound claimed.",
        "source_sha256": source_hashes(),
    }
    write_json(out / "RUN_SUMMARY.json", summary)
    if args.check:
        for name in (*NEW_REPORTS, "RUN_SUMMARY.json"):
            require_equal(read_json(out / name), read_json(ROOT / "results" / name), name)
        print("PASS all committed deterministic reports match", flush=True)
    print(json.dumps({key: value for key, value in summary.items() if key != "source_sha256"},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
