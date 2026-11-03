#!/usr/bin/env python3
"""Verify the compact licensed source snapshot, not the upstream theorem."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / "third_party" / "openai_math"
PIN = "4eaee87548250b2682affda7d05d947c05554bae"


def verify_snapshot():
    manifest = json.loads((SNAPSHOT / "manifest.json").read_text(encoding="utf-8"))
    if manifest["commit"] != PIN or manifest["license"]["spdx"] != "Apache-2.0":
        raise RuntimeError("Unexpected upstream source pin or license")
    unchanged, excerpts, total_bytes = 0, 0, 0
    seen = set()
    for record in manifest["files"]:
        relative = Path(record["path"])
        if relative.is_absolute() or ".." in relative.parts or relative.as_posix() in seen:
            raise RuntimeError("Invalid or duplicated snapshot path")
        seen.add(relative.as_posix())
        data = (SNAPSHOT / relative).read_bytes()
        sha = hashlib.sha256(data).hexdigest()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if (sha != record["sha256"] or len(data) != record["bytes"]
                or blob != record["snapshot_git_blob_sha1"]):
            raise RuntimeError(f"Snapshot bytes differ: {relative}")
        if record["transformation"] is None:
            if blob != record["upstream_git_blob_sha1"] or record["source_lines"] is not None:
                raise RuntimeError(f"Unchanged source provenance mismatch: {relative}")
            unchanged += 1
        else:
            source_lines = record["source_lines"]
            if (not isinstance(source_lines, list) or len(source_lines) != 2
                    or not 0 < source_lines[0] <= source_lines[1]):
                raise RuntimeError(f"Missing excerpt provenance: {relative}")
            excerpts += 1
        expected_url = (f"https://github.com/openai/math/blob/{PIN}/"
                        + record["upstream_path"])
        if record["upstream_url"] != expected_url:
            raise RuntimeError(f"Unpinned source link: {relative}")
        total_bytes += len(data)
    if "LICENSE" not in seen:
        raise RuntimeError("Missing third-party license")
    return {"commit": PIN, "files_hash_verified": len(seen),
            "unchanged_upstream_blobs_verified": unchanged,
            "marked_excerpts_verified": excerpts, "source_bytes": total_bytes,
            "scope": "Local provenance and source integrity only; not Lean compilation or theorem verification."}


if __name__ == "__main__":
    print(json.dumps(verify_snapshot(), indent=2))
