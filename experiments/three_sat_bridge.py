#!/usr/bin/env python3
"""Verify the elementary 3-CNF -> binary CNF + ternary XOR reduction.

The source oracle reads original literals directly. The local truth table checks
all 8 literal-truth inputs and all 8 helper assignments. Small complete target
truth tables separately verify projection and non-parsimonious model counts.
Decision-mode measurements expose this solver's increased observed rank.
"""

from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path

from pnp_lab.mixed import check_sat_witness, solve_mixed
from pnp_lab.reductions import three_cnf_to_two_cnf_xor


SUMMARY_FIELDS = (
    "status", "n_variables", "affine_consistent", "affine_dimension",
    "effective_rank", "quotient_cells", "checked_cells", "requested_exhaustive",
    "exhaustive", "satisfying_cells", "rejecting_cells", "model_count",
)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def raw_cnf_holds(cnf, values: tuple[int, ...]) -> bool:
    """Direct literal semantics, independent of the reduction and solver helpers."""
    return all(any(values[abs(literal) - 1] == int(literal > 0) for literal in clause)
               for clause in cnf)


def raw_xor_holds(rows, values: tuple[int, ...]) -> bool:
    return all(sum(value for index, value in enumerate(values) if mask & (1 << index)) % 2 == rhs
               for mask, rhs in rows)


def raw_target_holds(reduction, values: tuple[int, ...]) -> bool:
    return raw_xor_holds(reduction.affine.equations, values) and raw_cnf_holds(reduction.cnf, values)


def mask_of(values: tuple[int, ...]) -> int:
    return sum(value << index for index, value in enumerate(values))


def values_of(mask: int, n: int) -> tuple[int, ...]:
    return tuple((mask >> index) & 1 for index in range(n))


def validate_structure(reduction) -> dict:
    """Check fresh, disjoint helpers and the precise emitted clause/row shape."""
    n = len(reduction.original_variables)
    clauses = reduction.original_cnf
    nonempty = sum(bool(clause) for clause in clauses)
    empty = len(clauses) - nonempty
    target_variables = reduction.affine.variables
    _require(len(target_variables) == n + 3 * nonempty, "Unexpected number of target variables.")
    _require(target_variables[:n] == reduction.original_variables, "Original variable positions changed.")
    _require(len(set(target_variables)) == len(target_variables), "Helper names are not fresh.")
    _require(len(reduction.auxiliary_triples) == len(clauses), "Missing clause-to-helper correspondence.")
    helpers = set()
    expected_rows = []
    expected_cnf = []
    for clause, triple in zip(clauses, reduction.auxiliary_triples):
        if not clause:
            _require(triple is None, "An empty clause must be retained without helpers.")
            expected_cnf.append(())
            continue
        _require(triple is not None and len(triple) == len(set(triple)) == 3,
                 "A nonempty clause needs three distinct helpers.")
        _require(all(n <= column < len(target_variables) for column in triple),
                 "Helper columns overlap original variables or leave the scope.")
        _require(not helpers.intersection(triple), "Different clauses share a helper.")
        helpers.update(triple)
        expected_rows.append((sum(1 << column for column in triple), 0))
        padded = clause + (clause[-1],) * (3 - len(clause))
        expected_cnf.extend((literal, column + 1) for literal, column in zip(padded, triple))
    _require(helpers == set(range(n, len(target_variables))), "Unexpected unused helper columns.")
    _require(set(reduction.affine.equations) == set(expected_rows)
             and len(reduction.affine.equations) == nonempty,
             "Target XOR rows differ from the disjoint even-parity triples.")
    _require(reduction.cnf == tuple(expected_cnf), "Target binary clauses do not match literal/helper pairs.")
    observed_originals = {abs(literal) for clause in clauses for literal in clause}
    return {
        "source_variables": n,
        "source_clauses": len(clauses),
        "nonempty_source_clauses": nonempty,
        "empty_source_clauses": empty,
        "source_observed_variables": len(observed_originals),
        "target_variables": n + 3 * nonempty,
        "target_binary_clauses": 3 * nonempty,
        "target_empty_clauses": empty,
        "target_ternary_xor_equations": nonempty,
        "predicted_affine_dimension": n + 2 * nonempty,
        "predicted_observation_rank": len(observed_originals) + 2 * nonempty,
        "helpers_are_fresh_and_disjoint": True,
    }


def expected_extensions(cnf, values: tuple[int, ...]) -> int:
    """Count helper extensions from padded TRUE OCCURRENCES, not distinct names."""
    if not raw_cnf_holds(cnf, values):
        return 0
    result = 1
    for clause in cnf:
        padded = clause + (clause[-1],) * (3 - len(clause))
        true_occurrences = sum(values[abs(literal) - 1] == int(literal > 0) for literal in padded)
        _require(true_occurrences > 0, "A satisfying source clause has no true occurrence.")
        result *= 1 << (true_occurrences - 1)
    return result


def verify_local_bridge() -> dict:
    reduction = three_cnf_to_two_cnf_xor(("a", "b", "c"), ((1, 2, 3),))
    validate_structure(reduction)
    rows = []
    for literals in product((0, 1), repeat=3):
        valid_helpers = []
        for helpers in product((0, 1), repeat=3):
            definition = (sum(helpers) % 2 == 0
                          and all(literal or helper for literal, helper in zip(literals, helpers)))
            generated = raw_target_holds(reduction, literals + helpers)
            _require(generated == definition, "Generated gadget differs from its defining predicate.")
            if generated:
                valid_helpers.append(helpers)
        count = len(valid_helpers)
        true_occurrences = sum(literals)
        expected = 0 if true_occurrences == 0 else 1 << (true_occurrences - 1)
        _require(count == expected, "Local helper multiplicity mismatch.")
        _require(bool(count) == bool(any(literals)), "Local existential OR equivalence failed.")
        rows.append({
            "literal_truth_values": literals,
            "true_occurrences": true_occurrences,
            "valid_helper_assignments": valid_helpers,
            "extension_count": count,
            "predicted_extension_count": expected,
            "checks_passed": True,
        })
    return {
        "literal_truth_inputs": 8,
        "helper_assignments_per_input": 8,
        "complete_assignments_checked": 64,
        "source_model_count": 7,
        "target_model_count": sum(row["extension_count"] for row in rows),
        "rows": rows,
        "checks_passed": True,
    }


def _examples() -> tuple:
    return (
        ("positive_single_clause", ("a", "b", "c"), ((1, 2, 3),)),
        ("signed_shared_variables", ("a", "b", "c"), ((1, -2, 3), (-1, 2, -3))),
        ("signed_repeated_occurrences", ("a", "b"), ((1, 1, -2), (-1, 2, 2))),
        ("short_clause_padding", ("a", "b"), ((1,), (-1, 2))),
        ("unit_contradiction", ("a",), ((1,), (-1,))),
        ("four_clause_unsat", ("a", "b"),
         ((1, 2, 2), (1, -2, -2), (-1, 2, 2), (-1, -2, -2))),
        ("coupled_four_variables", ("a", "b", "c", "d"),
         ((1, 2, 3), (-1, -2, 4), (1, -3, -4), (-2, 3, -4))),
        ("unused_original_variable", ("a", "b", "c", "unused"), ((1, -2, 3),)),
        ("empty_formula", (), ()),
        ("empty_clause", (), ((),)),
    )


def verify_formula(name: str, variables: tuple[str, ...], cnf) -> dict:
    reduction = three_cnf_to_two_cnf_xor(variables, cnf)
    shape = validate_structure(reduction)
    n = len(variables)
    total_n = len(reduction.affine.variables)
    _require(n <= 7 and shape["predicted_affine_dimension"] <= 12,
             "This experiment intentionally limits source truth tables and quotient size.")
    expected_counts = [0] * (1 << n)
    source_models = []
    rejected_source_nonmodels = 0
    for values in product((0, 1), repeat=n):
        source_mask = mask_of(values)
        expected_counts[source_mask] = expected_extensions(cnf, values)
        if raw_cnf_holds(cnf, values):
            source_models.append(source_mask)
            lifted = reduction.lift_witness(source_mask)
            _require(raw_target_holds(reduction, values_of(lifted, total_n)),
                     f"{name}: lifted source witness fails raw target evaluation.")
            _require(check_sat_witness(reduction.affine, reduction.cnf, lifted),
                     f"{name}: lifted source witness fails the SAT checker.")
            _require(reduction.project_witness(lifted) == source_mask,
                     f"{name}: lift/project round trip changed the original assignment.")
        else:
            try:
                reduction.lift_witness(source_mask)
            except ValueError:
                rejected_source_nonmodels += 1
            else:
                raise AssertionError(f"{name}: source non-model was accepted by lift_witness.")
    source_models.sort()

    # This checks actual complete target assignments, not just a product formula
    # or the solver's quotient count, for the deliberately small target cases.
    full_target_oracle = None
    if total_n <= 9:
        actual_counts = [0] * (1 << n)
        for full in product((0, 1), repeat=total_n):
            if raw_target_holds(reduction, full):
                actual_counts[mask_of(full[:n])] += 1
        _require(actual_counts == expected_counts,
                 f"{name}: independent target projection/multiplicity mismatch.")
        full_target_oracle = {
            "assignments_checked": 1 << total_n,
            "extensions_by_source_mask": actual_counts,
            "target_model_count": sum(actual_counts),
        }

    decision = solve_mixed(reduction.affine, reduction.cnf, exhaustive=False,
                           include_trace=False, include_certificate=False)
    expected_status = "SAT" if source_models else "UNSAT"
    _require(decision["status"] == expected_status,
             f"{name}: mixed target decision differs from the source oracle.")
    _require(decision["requested_exhaustive"] is False, "Decision comparison must allow early SAT exit.")
    _require(decision["affine_dimension"] == shape["predicted_affine_dimension"],
             f"{name}: affine dimension differs from n + 2m_nonempty.")
    _require(decision["effective_rank"] == shape["predicted_observation_rank"],
             f"{name}: observed rank differs from observed_originals + 2m_nonempty.")
    projected_witness = None
    if expected_status == "SAT":
        full_mask = decision["witness_mask"]
        _require(raw_target_holds(reduction, values_of(full_mask, total_n)),
                 f"{name}: decision witness fails original target syntax.")
        projected_witness = reduction.project_witness(full_mask)
        _require(projected_witness in source_models, f"{name}: target witness projection is not a source model.")
    else:
        _require(decision["checked_cells"] == decision["quotient_cells"],
                 f"{name}: target decision did not finish the UNSAT quotient.")

    separate_counting_pass = not decision["exhaustive"]
    counting = (solve_mixed(reduction.affine, reduction.cnf, exhaustive=True,
                            include_trace=False, include_certificate=False)
                if separate_counting_pass else decision)
    _require(counting["exhaustive"] and counting["model_count"] == sum(expected_counts),
             f"{name}: complete target model count differs from the extension formula.")

    # On the nonempty-clause reduction image, each part is individually SAT.
    # The CNF witness uses all helpers = 1; the XOR witness uses all bits = 0.
    cnf_witness = sum(1 << column for triple in reduction.auxiliary_triples
                      if triple is not None for column in triple)
    binary_alone_sat = raw_cnf_holds(reduction.cnf, values_of(cnf_witness, total_n))
    xor_alone_sat = raw_xor_holds(reduction.affine.equations, (0,) * total_n)
    _require(xor_alone_sat, "The disjoint even-XOR part must be consistent.")
    _require(binary_alone_sat == (shape["empty_source_clauses"] == 0),
             "Unexpected CNF-only behavior.")
    return {
        "name": name,
        "shape": shape,
        "source_variables": variables,
        "source_cnf": cnf,
        "source_assignments_checked": 1 << n,
        "source_model_count": len(source_models),
        "source_model_masks": source_models,
        "source_models_lifted_and_checked": len(source_models),
        "source_nonmodels_rejected_by_lift": rejected_source_nonmodels,
        "auxiliary_triples_zero_based": reduction.auxiliary_triples,
        "target_xor_rows": reduction.affine.equations,
        "target_binary_cnf": reduction.cnf,
        "predicted_extensions_by_source_mask": expected_counts,
        "predicted_target_model_count": sum(expected_counts),
        "full_target_oracle": full_target_oracle,
        "decision": {field: decision[field] for field in SUMMARY_FIELDS},
        "decision_witness_mask": decision["witness_mask"],
        "projected_source_witness_mask": projected_witness,
        "separate_counting_pass": separate_counting_pass,
        "complete_counting": {field: counting[field] for field in SUMMARY_FIELDS},
        "cnf_part_alone_satisfiable": binary_alone_sat,
        "xor_part_alone_satisfiable": xor_alone_sat,
        "both_parts_individually_sat_but_mixed_unsat": binary_alone_sat and expected_status == "UNSAT",
        "checks_passed": True,
    }


def run_experiment() -> dict:
    local = verify_local_bridge()
    cases = [verify_formula(*example) for example in _examples()]
    highlighted = next(case for case in cases if case["name"] == "four_clause_unsat")
    _require(highlighted["shape"]["target_variables"] == 14
             and highlighted["decision"]["affine_dimension"] == 10
             and highlighted["decision"]["effective_rank"] == 10
             and highlighted["decision"]["checked_cells"] == 1024
             and highlighted["source_assignments_checked"] == 4,
             "The selected UNSAT bridge example must exhibit the documented counts.")
    return {
        "schema_version": 1,
        "experiment": "three_sat_bridge",
        "status": "verified",
        "claim_type": "Elementary decision-preserving and projection-preserving reduction; no novelty claim and no general-SAT speedup claimed.",
        "clause_identity": "(a OR b OR c) iff exists fresh u,v,w: (a OR u) AND (b OR v) AND (c OR w) AND (u XOR v XOR w = 0).",
        "padding": "Width-one and width-two clauses repeat the final literal to obtain three occurrences. Empty clauses remain empty and receive no helpers.",
        "model_count_warning": "Not parsimonious. A source assignment with s true occurrences in a padded clause has 2^(s-1) helper extensions when s>0, and zero when s=0. Multiply over independent helper triples.",
        "rank_identity": "With n original variables, m nonempty clauses, and p distinct observed original variables: target variable count n+3m, affine dimension n+2m, observed rank p+2m. When p=n, r=d and quotient compression removes no direction.",
        "local_truth_table": local["rows"],
        "local_truth_summary": {key: value for key, value in local.items() if key != "rows"},
        "formula_cases": cases,
        "summary": {
            "formula_cases": len(cases),
            "sat_cases": sum(case["decision"]["status"] == "SAT" for case in cases),
            "unsat_cases": sum(case["decision"]["status"] == "UNSAT" for case in cases),
            "source_assignments_checked": sum(case["source_assignments_checked"] for case in cases),
            "source_models_lifted_and_checked": sum(case["source_models_lifted_and_checked"] for case in cases),
            "full_target_assignments_checked": sum(case["full_target_oracle"]["assignments_checked"]
                                                    for case in cases if case["full_target_oracle"] is not None),
            "max_affine_dimension": max(case["decision"]["affine_dimension"] for case in cases),
            "highlighted_unsat_target_decision_cells": highlighted["decision"]["checked_cells"],
            "highlighted_unsat_original_assignments": highlighted["source_assignments_checked"],
        },
        "not_claimed": [
            "A novel NP-completeness result or a novel clause gadget.",
            "A polynomial-time algorithm for general SAT or P versus NP resolution.",
            "Preservation of model counts or of a uniform distribution on models.",
            "A lower bound for other solvers or a proof that the example is intrinsically difficult.",
            "End-to-end Lean verification of the Python reduction, solver, encoding, or complexity analysis.",
        ],
        "all_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", required=True, type=Path)
    args = parser.parse_args()
    payload = run_experiment()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    destination = args.out_dir / "three_sat_bridge.json"
    destination.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True, indent=2) + "\n",
                           encoding="utf-8")
    print(json.dumps({"status": "verified", "output": str(destination),
                      **payload["summary"]}, sort_keys=True))


if __name__ == "__main__":
    main()
