#!/usr/bin/env python3
"""Optional pinned PySAT/DRAT experiment, separate from stdlib reproduction.

Requires requirements-cdcl.txt and a C compiler. Proofs/checker logs stay in
--out-dir; cdcl_audit.json records hashes and the verified outcomes.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from pnp_lab.cdcl_audit import (checked_model, dimacs, formula_hash, regenerate,
                                summarize, verify_checker_source, verify_drat)
from pnp_lab.sat_scaling import (brute_force, check_row_contradiction, gaussian,
                                graph_xor_cnf, recognize_xor)

PROTOCOL = dict(version="cdcl-audit-v1", solvers=["g42", "cadical195"],
                python_sat="1.9.dev21", requested_conflict_budget=25_000,
                replicates=16, random_sizes=[96, 144, 192, 240, 288, 336],
                xor_sizes=[36, 48, 60, 72, 84, 96],
                scope="Finite algorithm/distribution-specific counts, no P-vs-NP probability",
                pilot="Excluded seed 29091+n; random n=96,192,288 and XOR n=36,54,72")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(args):
    import pysat
    import pysolvers
    from pysat.solvers import Solver
    if pysat.__version__ != PROTOCOL["python_sat"]:
        raise RuntimeError("Install the exact requirements-cdcl.txt versions")
    out = args.out_dir.resolve()
    artifacts = out / "certificates"
    artifacts.mkdir(parents=True, exist_ok=True)
    manifest = verify_checker_source(ROOT)
    checker = out / "drat-trim"
    compile_command = [args.cc, "-O2", "-std=gnu99", "third_party/drat_trim/drat-trim.c", "-o", str(checker)]
    subprocess.run(compile_command, cwd=ROOT, check=True, capture_output=True, text=True)
    provenance = dict(python=platform.python_version(), machine=platform.machine(),
                      system=platform.system(), pysat=pysat.__version__,
                      native_solver_sha256=sha(pysolvers.__file__),
                      checker_source=manifest, checker_binary_sha256=sha(checker),
                      compiler=subprocess.check_output([args.cc, "--version"], text=True).splitlines()[0],
                      compiler_flags=["-O2", "-std=gnu99"])

    def solve(n, clauses, solver, label):
        cnf = artifacts / f"{label}.cnf"
        cnf.write_text(dimacs(n, clauses))
        with Solver(name=solver, bootstrap_with=clauses, with_proof=True) as instance:
            instance.conf_budget(PROTOCOL["requested_conflict_budget"])
            answer = instance.solve_limited()
            stats = instance.accum_stats()
            status = "UNKNOWN" if answer is None else "SAT" if answer else "UNSAT"
            witness = proof_hash = None
            proof_lines = 0
            if status == "SAT":
                witness = checked_model(n, clauses, instance.get_model())
            elif status == "UNSAT":
                proof = instance.get_proof()
                if proof is None:
                    raise RuntimeError("UNSAT without a proof stream")
                path = artifacts / f"{label}.{solver}.drat"
                path.write_text("\n".join(proof) + "\n")
                verify_drat(checker, cnf, path, artifacts / f"{label}.{solver}.check.log")
                proof_hash = sha(path)
                proof_lines = len(proof)
            return dict(solver=solver, status=status, witness=witness, **stats,
                        proof_sha256=proof_hash, proof_lines=proof_lines,
                        certificate_checked=status != "UNKNOWN")

    # Independent truth-table checks, including both outcomes and zero clauses.
    universe = list(product((1, -1), (2, -2), (3, -3)))
    controls = 0
    for mask in range(256):
        clauses = [c for i, c in enumerate(universe) if mask & (1 << i)]
        expected = "SAT" if brute_force(3, clauses) is not None else "UNSAT"
        for solver in PROTOCOL["solvers"]:
            answer = solve(3, clauses, solver, f"truth-{mask}")
            assert answer["status"] == expected
            controls += 1
    for odd in (False, True):
        clauses = graph_xor_cnf(12, odd, 20261107)
        expected = "UNSAT" if odd else "SAT"
        for solver in PROTOCOL["solvers"]:
            assert solve(12, clauses, solver, f"parity-{int(odd)}")["status"] == expected
            controls += 1
    bad_cnf = artifacts / "negative-control.cnf"
    bad_proof = artifacts / "negative-control.drat"
    bad_cnf.write_text(dimacs(2, [(1, 2)]))
    bad_proof.write_text("0\n")
    try:
        verify_drat(checker, bad_cnf, bad_proof, artifacts / "negative-control.log")
    except RuntimeError:
        pass
    else:
        raise AssertionError("checker accepted a false proof on a satisfiable formula")
    print(f"PASS {controls} independent truth-table/parity controls and false-proof rejection", flush=True)

    baseline_path = ROOT / "results/sat_scaling.json"
    baseline = json.loads(baseline_path.read_text())
    paired = {}
    for record in baseline["records"]:
        key = (record["family"], record["n"], record["replicate"])
        if key not in paired:
            paired[key] = {k: record[k] for k in ("family", "n", "replicate", "seed", "formula_sha256")}
            paired[key]["baseline_answers"] = set()
            paired[key]["previously_censored_runs"] = 0
        if record["status"] == "UNKNOWN":
            paired[key]["previously_censored_runs"] += 1
        else:
            paired[key]["baseline_answers"].add(record["status"])
    assert len(paired) == 416
    cases = [dict(panel="paired", **case) for case in paired.values()]
    families = ["random_3sat_4.25", "random_3sat_6", "graph_xor_odd"]
    for family in families:
        for n in PROTOCOL["xor_sizes" if family == "graph_xor_odd" else "random_sizes"]:
            for replicate in range(PROTOCOL["replicates"]):
                key = f'{PROTOCOL["version"]}:{family}:{n}:{replicate}'
                seed = int(hashlib.sha256(key.encode()).hexdigest()[:16], 16)
                cases.append(dict(panel="extended", family=family, n=n,
                                  replicate=replicate, seed=seed))
    records = []
    algebraic = []
    for case in cases:
        n, family = case["n"], case["family"]
        clauses = regenerate(family, n, case["seed"])
        digest = formula_hash(clauses)
        if case["panel"] == "paired":
            assert digest == case["formula_sha256"]
            assert len(case["baseline_answers"]) == 1
        label = f'{case["panel"]}-{family}-{n}-{case["replicate"]}'
        statuses = set()
        for solver in PROTOCOL["solvers"]:
            result = solve(n, clauses, solver, label)
            if result["status"] != "UNKNOWN":
                statuses.add(result["status"])
            assert len(statuses) <= 1
            if case["panel"] == "paired":
                assert not statuses or statuses == case["baseline_answers"]
            records.append(dict(**{k: case[k] for k in ("panel", "family", "n", "replicate", "seed")},
                                formula_sha256=digest, clauses=len(clauses),
                                previously_censored_runs=case.get("previously_censored_runs", 0), **result))
        if family == "graph_xor_odd":
            equations = recognize_xor(n, clauses)
            assert equations is not None
            result = gaussian(n, equations)
            assert result["status"] == "UNSAT"
            assert check_row_contradiction(equations, result["contradiction"])
            assert not statuses or statuses == {"UNSAT"}
            algebraic.append(dict(panel=case["panel"], n=n, replicate=case["replicate"],
                                  status="UNSAT", row_xors=result["row_xors"], certificate_checked=True))
        if case["replicate"] == 15:
            print(f'PASS {case["panel"]} {family} n={n}', flush=True)
    return dict(protocol=PROTOCOL, provenance=provenance, baseline_report_sha256=sha(baseline_path),
                source_sha256={p: sha(ROOT / p) for p in
                               ("scripts/run_cdcl_audit.py", "src/pnp_lab/cdcl_audit.py",
                                "src/pnp_lab/sat_scaling.py", "requirements-cdcl.txt")},
                records=records, summaries=summarize(records), algebraic_controls=algebraic,
                independent_small_controls=controls, checker_negative_control_passed=True,
                counts=dict(sorted(Counter(r["status"] for r in records).items())),
                all_checks_passed=True, p_vs_np_resolved=False, p_vs_np_probability=None,
                scope="Native counters for named implementations on named distributions only")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "reproduced/cdcl")
    parser.add_argument("--cc", default="gcc")
    parser.add_argument("--check", type=Path, help="Compare the complete deterministic report with this file")
    args = parser.parse_args()
    report = run(args)
    (args.out_dir / "cdcl_audit.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    if args.check:
        if report != json.loads(args.check.read_text()):
            raise RuntimeError("CDCL report differs; versions/build/platform are included")
        print("PASS CDCL deterministic report matches", flush=True)
    print(json.dumps(dict(counts=report["counts"], scope=report["scope"])), flush=True)


if __name__ == "__main__":
    main()
