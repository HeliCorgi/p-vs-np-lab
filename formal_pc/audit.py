#!/usr/bin/env python3
"""Verify pinned sources, then ask Lean for explicit transitive axiom sets.

The source-integrity check does not claim to compile Lean. The full mode runs
after `lake build ProofLab` inside this package. Standard Mathlib caches may be
used for dependencies; this is not a claim of independent kernel replay.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
UPSTREAM = "25239211058ef718402a908b3272f01480c159c4"
MATHLIB = "67248ba34806c60bf24b5e99f0f09946ffc465c9"


def verify_snapshot() -> dict:
    manifest = json.loads((PACKAGE / "third_party/noemesis/manifest.json").read_text())
    if manifest["commit"] != UPSTREAM or manifest["license"] != "MIT":
        raise RuntimeError("Unexpected foundation revision or license")
    if len(manifest["files"]) != 3:
        raise RuntimeError("The audited foundation snapshot must contain exactly three files")
    for entry in manifest["files"]:
        data = (ROOT / entry["path"]).read_bytes()
        blob = b"blob " + str(len(data)).encode() + b"\0" + data
        if (len(data) != entry["bytes"]
                or hashlib.sha256(data).hexdigest() != entry["sha256"]
                or hashlib.sha1(blob).hexdigest() != entry["git_blob_sha1"]):
            raise RuntimeError(f"Pinned foundation changed: {entry['path']}")
    lock = json.loads((PACKAGE / "lake-manifest.json").read_text())
    mathlib = [p for p in lock["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB:
        raise RuntimeError("Unexpected Mathlib revision")
    if (PACKAGE / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.0-rc2":
        raise RuntimeError("Unexpected ordinary-PC Lean toolchain")
    for name in ("LICENSE", "UPSTREAM_LICENSE"):
        if not (PACKAGE / "third_party/noemesis" / name).read_text().strip():
            raise RuntimeError(f"Missing upstream license: {name}")
    return {
        "files": len(manifest["files"]),
        "bytes": sum(e["bytes"] for e in manifest["files"]),
        "upstream_commit": UPSTREAM,
        "mathlib_commit": MATHLIB,
        "scope": "byte integrity only; Lean build and theorem axiom audit are separate gates",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-snapshot-only", action="store_true")
    args = parser.parse_args()
    snapshot = verify_snapshot()
    print(f"PASS {snapshot['files']} pinned ordinary-PC foundation files ({snapshot['bytes']} bytes)",
          flush=True)
    if args.verify_snapshot_only:
        return
    names = json.loads((PACKAGE / "audit_theorems.json").read_text())
    if not names or len(names) != len(set(names)):
        raise RuntimeError("Empty or duplicated theorem audit list")
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", n) for n in names):
        raise RuntimeError("Malformed theorem name")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=PACKAGE, delete=False) as query:
        query.write("import ProofLab\n\n")
        query.writelines(f"#print axioms {name}\n" for name in names)
        query_path = Path(query.name)
    try:
        process = subprocess.run(["lake", "env", "lean", query_path.name], cwd=PACKAGE,
                                 capture_output=True, text=True, timeout=180)
    finally:
        query_path.unlink(missing_ok=True)
    print(process.stdout, end="")
    if process.returncode:
        raise RuntimeError(process.stderr + "\nLean axiom query failed")
    pattern = r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    entries = list(re.finditer(pattern, process.stdout))
    parsed = {m.group(1): {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
              for m in entries}
    if set(parsed) != set(names) or len(entries) != len(names):
        raise RuntimeError(f"Unexpected or missing audit entries: {set(parsed) ^ set(names)}")
    for theorem, axioms in parsed.items():
        if axioms - ALLOWED:
            raise RuntimeError(f"Unapproved axioms in {theorem}: {axioms - ALLOWED}")
    print(f"PASS {len(names)} ordinary-PC theorem axiom audits; only standard logical axioms are allowed")


if __name__ == "__main__":
    main()
