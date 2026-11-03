#!/usr/bin/env python3
"""Reproduce the finite experiments using only Python's standard library."""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "reproduced")
    args = parser.parse_args()
    out = args.out_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((ROOT / "upstream/SOURCE_MANIFEST.json").read_text())
    source_root = ROOT / "upstream/hadwiger-nelson-lab"
    for item in manifest["files"]:
        data = (source_root / item["path"]).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if digest != item["sha256"]:
            raise RuntimeError("Changed upstream input: " + item["path"])
    commands = [
        [sys.executable, str(source_root / "tools/check_separator_left_proof_tree.py"),
         "--repo-root", str(source_root), "--out", str(out / "hn_existing_checker.json")],
        [sys.executable, str(ROOT / "boundary_compression.py"), "--out-dir", str(out)],
        [sys.executable, str(ROOT / "transparent_gluing.py"),
         "--out-dir", str(out / "transparent-gluing")],
        [sys.executable, str(ROOT / "fixedpoint_sat.py"),
         "--out-dir", str(out / "fixedpoint")],
    ]
    for index, command in enumerate(commands):
        completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        (out / f"run-{index + 1}.log").write_text(completed.stdout + completed.stderr)
        if completed.returncode:
            raise RuntimeError(f"Experiment {index + 1} failed; see run-{index + 1}.log")
    load = lambda path: json.loads((out / path).read_text())
    hn = load("hn_existing_checker.json")
    compression = load("boundary_compression.json")
    gluing = load("transparent-gluing/transparent_gluing_results.json")
    fixedpoint = load("fixedpoint/fixedpoint_sat_results.json")
    summary = {
        "status": "PASS",
        "python_version": platform.python_version(),
        "upstream_commit": manifest["commit"],
        "upstream_files_hash_verified": len(manifest["files"]),
        "upstream_composition_checks": len(hn["checks"]),
        "upstream_composition_checks_passed": hn["all_checks_passed"],
        "boundary_states_rechecked": compression["canonical_universe_count"],
        "boundary_minimum_additional_clauses": compression["minimum_clause_count"],
        "boundary_minimum_covers": compression["minimum_syntactic_cover_count"],
        "gluing_assignments_enumerated": gluing["total_assignments_examined"],
        "gluing_checks_passed": gluing["all_checks_passed"],
        "fixedpoint_cases": len(fixedpoint["cases"]),
        "fixedpoint_self_checks_passed": fixedpoint["self_checks"]["passed"],
        "fixedpoint_runs_completed_without_failed_assertions": True,
        "scope": "Finite experiments and conditional saved-relation checks; no P-versus-NP resolution.",
    }
    if not all((summary["upstream_composition_checks_passed"],
                summary["gluing_checks_passed"], summary["fixedpoint_self_checks_passed"],
                compression["status"] == "PASS")):
        raise RuntimeError("A component did not report success")
    (out / "RUN_SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
