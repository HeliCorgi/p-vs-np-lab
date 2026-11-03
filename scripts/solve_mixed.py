#!/usr/bin/env python3
"""Decide an explicit JSON XOR+CNF instance, with honest budget exhaustion.

Variables are listed explicitly. DIMACS literal +/-i refers to variables[i-1].
Exit status: 0 for SAT or UNSAT, 2 for UNKNOWN, 1 for invalid input/check failure.
The default stops at the first model. --count-models enumerates all quotient
cells. There is no default search budget. This is not a polynomial-time solver.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from pnp_lab.affine import AffineRelation
from pnp_lab.mixed import check_sat_witness, check_unsat_certificate, solve_mixed


class SolverArgumentParser(argparse.ArgumentParser):
    def error(self, message):
        raise ValueError("arguments: " + message)


def load_problem(path: Path):
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or set(value) - {"variables", "xor", "cnf"}:
        raise ValueError("Input must be an object containing only variables, xor, and cnf.")
    variables = value.get("variables")
    if not isinstance(variables, list):
        raise ValueError("variables must be an explicit list of distinct names.")
    xor_rows = value.get("xor", [])
    cnf = value.get("cnf", [])
    if not isinstance(xor_rows, list):
        raise ValueError("xor must be a list of equations.")
    if not isinstance(cnf, list) or any(not isinstance(c, list) for c in cnf):
        raise ValueError("cnf must be a list of lists of DIMACS literals.")
    named = []
    for row in xor_rows:
        if not isinstance(row, dict) or set(row) != {"terms", "rhs"}:
            raise ValueError("Each XOR equation must have exactly terms and rhs.")
        if not isinstance(row["terms"], list):
            raise ValueError("XOR terms must be a list of variable names.")
        named.append((row["terms"], row["rhs"]))
    affine = AffineRelation.from_named(variables, named)
    return affine, tuple(tuple(clause) for clause in cnf)


def main() -> int:
    parser = SolverArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--count-models", action="store_true")
    parser.add_argument("--max-cells", type=int)
    parser.add_argument("--trace", action="store_true")
    parser.add_argument("--certificate", action="store_true",
                        help="Include an UNSAT certificate; its size may be exponential.")
    parser.add_argument("--verify-certificate", action="store_true",
                        help="Also generate and independently check an UNSAT certificate.")
    parser.add_argument("--out", type=Path, help="Write JSON here instead of stdout.")
    try:
        args = parser.parse_args()
        affine, cnf = load_problem(args.input)
        result = solve_mixed(
            affine, cnf, exhaustive=args.count_models, max_cells=args.max_cells,
            include_trace=args.trace,
            include_certificate=args.certificate or args.verify_certificate,
        )
        if result["status"] == "SAT":
            if not check_sat_witness(affine, cnf, result["witness_mask"]):
                raise RuntimeError("Returned SAT witness failed direct evaluation.")
        if result["status"] == "UNSAT" and args.verify_certificate:
            if not check_unsat_certificate(affine, cnf, result["certificate"]):
                raise RuntimeError("Returned UNSAT certificate failed verification.")
        text = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
        if args.out is None:
            print(text, end="")
        else:
            args.out.write_text(text, encoding="utf-8")
        return 2 if result["status"] == "UNKNOWN" else 0
    except (ValueError, TypeError, KeyError, OSError, RuntimeError) as error:
        print(json.dumps({"status": "ERROR", "error": str(error)}), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
