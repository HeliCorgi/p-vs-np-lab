#!/usr/bin/env python3
"""Prepare an isolated, pinned-source Lean audit of the upstream SAT endpoint.

This copies the actual transitive OAI import closure without changing proof
sources. It replaces the monorepo's unrelated dependency/bootstrap configuration
with a minimal Mathlib-pinned harness. Preparation is NOT proof verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

UPSTREAM_COMMIT = "4eaee87548250b2682affda7d05d947c05554bae"
MATHLIB_COMMIT = "d13f23b723b8a846827a245b89c10fc7d3f11612"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
TARGET = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final"
THEOREM = "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat"
EXTERNAL_ROOTS = {"Mathlib", "Init", "Std", "Lean", "Lake", "Aesop", "Batteries",
                  "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph"}
# Checked against mathlib's own manifest at MATHLIB_COMMIT, as well as the
# pinned OAI manifest. Keep the exact dependency closure, not unrelated projects.
DEPENDENCY_REVISIONS = {
    "mathlib": MATHLIB_COMMIT,
    "plausible": "118aa17ee84656b8bd727fef7c458ee8c833385c",
    "LeanSearchClient": "ddf04cf3949fa556442341e87d47f9f6e6074707",
    "importGraph": "e928b72544873815af278d38681b31c0293588e3",
    "proofwidgets": "106ff4fafc74ef4ac99d81dbf3ab399118f497a5",
    "aesop": "355695d523e41d0554926416cba2a2b3544fbbc9",
    "Qq": "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259",
    "batteries": "f2effa3d803fda822b1f97b806c47cf2adfbcbc2",
    "Cli": "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204",
}


def uncommented_lines(text):
    """Yield uncommented header lines lazily; the caller stops before the body."""
    result = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1; i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1; i += 2
        elif not depth and text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            c = text[i]
            if c == "\n":
                yield "".join(result)
                result = []
            else:
                result.append(c if not depth else " ")
            i += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    if result:
        yield "".join(result)


def imports(text):
    found = []
    for line in uncommented_lines(text):
        line = line.strip()
        if not line or line in {"module", "prelude"}:
            continue
        match = re.fullmatch(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)", line)
        if not match:
            break  # Lean imports belong to the header.
        for name in match.group(1).split():
            if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*(?:\.[A-Za-z_0-9']+)*", name):
                raise ValueError(f"Unsupported import syntax: {line}")
            found.append(name)
    return found


def prepare(source, out):
    source = source.resolve()
    head = subprocess.check_output(["git", "-C", str(source.parent), "rev-parse", "HEAD"],
                                   text=True).strip()
    if head != UPSTREAM_COMMIT:
        raise ValueError(f"Expected upstream {UPSTREAM_COMMIT}, got {head}")
    if (source / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError("Unexpected upstream Lean version")
    if out.exists() and any(out.iterdir()):
        raise ValueError("Audit output directory must be empty")
    out.mkdir(parents=True, exist_ok=True)
    pending, seen, records, external = [TARGET], set(), [], set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = Path(*module.split(".")).with_suffix(".lean")
        data = (source / path).read_bytes()
        dependencies = imports(data.decode("utf-8"))
        for dependency in dependencies:
            root = dependency.split(".", 1)[0]
            if root == "OAI":
                pending.append(dependency)
            elif root in EXTERNAL_ROOTS:
                external.add(dependency)
            else:
                raise ValueError(f"Unreviewed external import: {dependency} in {module}")
        dest = out / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        records.append({"module": module, "upstream_path": "lean/" + path.as_posix(),
                        "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
                        "git_blob_sha1": hashlib.sha1(b"blob " + str(len(data)).encode()
                                                       + b"\0" + data).hexdigest(),
                        "imports": dependencies})
    (out / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (out / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\npackage PnpUpstreamAudit where\n'
        '  fixedToolchain := true\n  leanOptions := #[⟨`autoImplicit, false⟩]\n'
        'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "'
        + MATHLIB_COMMIT + '"\nlean_lib OAI\n')
    upstream_manifest = json.loads((source / "lake-manifest.json").read_text())
    packages = [p for p in upstream_manifest["packages"] if p["name"] in DEPENDENCY_REVISIONS]
    if {p["name"]: p["rev"] for p in packages} != DEPENDENCY_REVISIONS:
        raise ValueError("Unexpected upstream Mathlib dependency revisions")
    lake_manifest = {"version": upstream_manifest["version"], "packagesDir": ".lake/packages",
                     "packages": packages, "name": "PnpUpstreamAudit", "lakeDir": ".lake",
                     "fixedToolchain": True}
    (out / "lake-manifest.json").write_text(json.dumps(lake_manifest, indent=2) + "\n")
    (out / "Audit.lean").write_text("import " + TARGET + "\n#check " + THEOREM
                                    + "\n#print axioms " + THEOREM + "\n")
    (out / "UPSTREAM_LICENSE").write_bytes((source.parent / "LICENSE").read_bytes())
    manifest = {
        "schema_version": 1, "repository": "openai/math", "commit": head,
        "target_module": TARGET, "target_theorem": THEOREM, "toolchain": TOOLCHAIN,
        "mathlib_commit": MATHLIB_COMMIT,
        "dependency_revisions": DEPENDENCY_REVISIONS,
        "harness_scope": "Unmodified transitive OAI sources; isolated Mathlib-pinned Lake configuration. Not the full upstream monorepo or comparator.",
        "kernel_build_status": "not_run_by_preparation", "comparator_status": "not_run",
        "module_count": len(records), "source_bytes": sum(r["bytes"] for r in records),
        "external_imports": sorted(external), "files": sorted(records, key=lambda r: r["module"]),
    }
    (out / "source_manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v for k, v in manifest.items() if k not in {"files", "external_imports"}}, indent=2))
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-dir", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    prepare(args.upstream_dir, args.out_dir)


if __name__ == "__main__":
    main()
