#!/usr/bin/env python3
"""Exact audit of one necessary parameter gate in openai/math family 378.

This does not execute, refute, or verify the upstream subexponential algorithm.
It checks its concrete integer schedule, including a ceiling-log discontinuity.
The complete large-input cutoff has additional conditions and is not computed.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = "4eaee87548250b2682affda7d05d947c05554bae"


def clog2(n):
    if type(n) is not int or n < 0:
        raise ValueError("Expected a nonnegative integer")
    return (n - 1).bit_length() if n > 1 else 0


def schedule_at_lambda(lam):
    nu = clog2(lam)
    return isqrt(lam) // (nu * nu) if nu else 0


def first_feasible_lambda():
    intervals = []
    nu = 3  # n >= 20 implies lambda >= 5 and nu >= 3.
    while True:
        lower, upper = (1 << (nu - 1)) + 1, 1 << nu
        required = 4 * nu ** 4
        candidate = max(lower, required, 5)
        intervals.append({"nu": nu, "lambda_lower": lower, "lambda_upper": upper,
                          "lambda_required": required, "interval_has_solution": candidate <= upper})
        if candidate <= upper:
            return candidate, nu, intervals
        nu += 1


def power_plus_one_digits(exponent):
    """Guess a digit count with Decimal, then verify it by exact integer bounds."""
    with localcontext() as ctx:
        ctx.prec = 80
        digits = int(Decimal(exponent) * Decimal(2).log10()) + 1
    value = (1 << exponent) + 1
    assert 10 ** (digits - 1) <= value < 10 ** digits
    return digits


def run():
    lam, nu, intervals = first_feasible_lambda()
    assert (lam, nu) == (521284, 19)
    assert schedule_at_lambda(lam) == 2
    assert all(schedule_at_lambda(x) < 2 for x in range(5, lam))
    assert schedule_at_lambda(524288) == 2
    assert schedule_at_lambda(524289) == 1
    assert schedule_at_lambda(639999) == 1
    assert schedule_at_lambda(640000) == 2
    # For nu>=21, 2^(nu-1)>=4nu^4 follows from this base and
    # ((nu+1)/nu)^4 <= (22/21)^4 < 2. This is an all-size argument.
    assert 2 ** 20 >= 4 * 21 ** 4
    assert 22 ** 4 < 2 * 21 ** 4
    samples = []
    for x in (5, 10, 100, 1000, 10000, 100000, 500000, 521283, 521284,
              524288, 524289, 639999, 640000, 1048576, 1048577):
        samples.append({"lambda": x, "nu": clog2(x), "schedule": schedule_at_lambda(x),
                        "first_n_with_this_lambda": f"2^{x - 1} + 1"})
    return {
        "schema_version": 1, "all_checks_passed": True,
        "upstream_repository": "openai/math", "upstream_commit": PIN,
        "source": "lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Asymptotics.lean",
        "definitions": {"lambda": "ceil(log2(n))", "nu": "ceil(log2(lambda))",
                        "schedule": "floor(sqrt(lambda)) // nu^2", "domain": "n >= 20"},
        "condition": "schedule >= 2 iff lambda >= 4*nu^4",
        "first_possible": {"lambda": lam, "nu": nu,
                           "n_symbolic": f"2^{lam - 1} + 1",
                           "n_decimal_digits": power_plus_one_digits(lam - 1),
                           "all_smaller_lambdas_checked": lam - 5},
        "nonmonotone_drop": {"lambda_before": 524288, "schedule_before": 2,
                              "lambda_after": 524289, "schedule_after": 1},
        "eventual_schedule_gate": {"lambda": 640000, "n_symbolic": "2^639999 + 1",
                                    "n_decimal_digits": power_plus_one_digits(639999),
                                    "all_size_reason": "nu=20 succeeds from lambda=640000; for nu>=21, the power-of-two lower boundary dominates 4*nu^4 by the stated base and ratio inequality."},
        "intervals_before_first_success": intervals, "samples": samples,
        "total_algorithm_cutoff_computed": False,
        "claim_scope": "This is one necessary schedule condition, not the complete upstream cutoff or an executable implementation of the claimed theorem. A finite but enormous fallback is compatible with a uniform asymptotic theorem.",
        "asymptotic_scope": "The published subexponential upper bound does not supply a polynomial upper bound. It is not by itself a superpolynomial lower bound on the algorithm.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "results")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    report = run()
    (args.out_dir / "upstream_parameters.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"all_checks_passed": True, "first_possible": report["first_possible"],
                      "nonmonotone_drop": report["nonmonotone_drop"],
                      "total_algorithm_cutoff_computed": False}, indent=2))


if __name__ == "__main__":
    main()
