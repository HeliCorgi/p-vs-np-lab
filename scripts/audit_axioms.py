#!/usr/bin/env python3
"""Ask Lean for the actual transitive axiom dependencies of the main theorems.

This runs after `lake build Formal`. It rejects missing audit entries and any
axiom outside Lean's three standard logical axioms, including proof holes or
native evaluation trust axioms. It does not claim an independent Lean kernel.
"""

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = {
    "BoundaryLab.Star5.star_iff_collision",
    "BoundaryLab.Star5.valid_rejecting_clause_contains_all_equalities",
    "BoundaryLab.Star5.every_exact_CNF_has_all_equalities_clause",
    "BoundaryLab.Star5.star_iff_allEqualityClause",
    "BoundaryLab.Star5.allEqualityClause_length",
    "BoundaryLab.Star5.allEqualityClause_nodup",
    "BoundaryLab.Composition.independent_interiors_compose",
    "BoundaryLab.Composition.independent_interiors_with_boundary_constraint",
    "BoundaryLab.Quotient.quotient_sat_iff",
    "BoundaryLab.Quotient.lifted_witness_is_valid",
    "BoundaryLab.Quotient.quotient_unsat_iff",
    "BoundaryLab.Quotient.finite_scan_exact",
    "BoundaryLab.Quotient.bitVectors_length",
    "BoundaryLab.ThreeSatBridge.clause_iff_gadget",
    "BoundaryLab.ThreeSatBridge.clauses_iff_independent_helpers",
    "BoundaryLab.ThreeSatBridge.formula_sat_iff",
    "BoundaryLab.ExactlyOneParity.cover_exclusions_imply_parity",
    "BoundaryLab.ExactlyOneParity.parity_of_evaluated_literals",
    "BoundaryLab.ExactlyOneParity.signed_exactly_one_implies_parity",
    "BoundaryLab.ExactlyOneParity.strengthen_preserves_models",
    "BoundaryLab.ExactlyOneParity.strengthen_preserves_sat",
    "BoundaryLab.BridgeAffineBarrier.row_flip_of_mem",
    "BoundaryLab.BridgeAffineBarrier.coordinate_separation_forces_trivial_row",
    "BoundaryLab.BridgeAffineBarrier.bridge_coordinate_separation",
    "BoundaryLab.BridgeAffineBarrier.bridge_has_no_nontrivial_affine_equation",
    "BoundaryLab.JointXorClause.joint_clause_of_forced_parity_conflict",
    "BoundaryLab.JointXorClause.strengthen_preserves_models",
    "BoundaryLab.JointXorClause.strengthen_preserves_sat",
    "BoundaryLab.AffineFrontier.reach_iff_recorded_choices",
    "BoundaryLab.AffineFrontier.pruned_iff_reach",
    "BoundaryLab.AffineFrontier.suffix_observation_forced",
    "BoundaryLab.AffineFrontier.absorb_exact_image",
    "BoundaryLab.HoleFibers.three_pairs_escape",
    "BoundaryLab.HoleFibers.two_pairs_blocked_iff_cross",
    "BoundaryLab.HoleFibers.two_point_fiber_puncture",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    process = subprocess.run(["lake", "env", "lean", "scripts/PrintAxioms.lean"],
                             cwd=ROOT, capture_output=True, text=True)
    print(process.stdout, end="")
    if process.returncode:
        raise RuntimeError(process.stderr + "\nLean axiom query failed")
    parsed = {}
    pattern = r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    for match in re.finditer(pattern, process.stdout):
        parsed[match.group(1)] = {a.strip() for a in (match.group(2) or "").split(",") if a.strip()}
    if set(parsed) != THEOREMS:
        raise RuntimeError(f"Unexpected or missing audit entries: {set(parsed) ^ THEOREMS}")
    for theorem, axioms in parsed.items():
        if axioms - ALLOWED:
            raise RuntimeError(f"Unapproved axioms in {theorem}: {axioms - ALLOWED}")
    print(f"PASS {len(parsed)} theorem axiom audits; only standard logical axioms are allowed")


if __name__ == "__main__":
    main()
