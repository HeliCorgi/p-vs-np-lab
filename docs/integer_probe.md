# Conditional integer refutation, with an explicit ceiling

[Implementation](../src/pnp_lab/integer_probe.py) · [tests](../tests/test_integer_probe.py) · [reproducible controls](../experiments/integer_probe.py) · [report](../results/integer_probe.json).

The new [integer oracle](integer_hull.md) is a sound but incomplete refuter. A failed-value inference asks whether the original formula restricted to a single Boolean value has a checked contradiction. If it does, the opposite value holds in every original model. Learn that unit, restart, and continue. An integer solution to a relaxation never justifies a Boolean choice.

This is the established failed-literal principle with a stronger arithmetic oracle, not a new algorithmic principle. Unlike the previous [one-bit parity pass](case_parity.md), the oracle discovers its modulus and a forced unit may feed later calls. The two methods overlap on ordinary parity examples.

## Certificate and cost

The proof records a sequence of assumed literals and a checked refutation of each restriction. The checker restricts the original clauses using **only previously learned units** and the current assumption. It never uses the unit being proved, a future unit, or a claimed integer solution. Each step may replay private resolution before checking the integer certificate. A final refutation is checked with the learned units and no additional assumption. Clause order and original variable names are retained; zero-step normalization must not change proof clause indices.

At most n distinct units can be learned. Each round scans at most 2n candidate values, so there are at most (n+1)(2n+1) oracle calls without an outer cap. This is a bound on the number of incomplete calls, **not a polynomial-time SAT algorithm**. Local-table size, discovery, integer coefficient bits, inner operation caps, and the total proof size are separate costs. The CLI caps this explicit method at 32 calls by default. UNKNOWN and a budget cap do not imply SAT, UNSAT, or a forced bit. The automatic conservation gate tries the root integer relaxation, but does not silently run this quadratic family of probes.

## Raw guarded-flow test

Take independent contradictory binary and ternary flows F2 and F3. The formula

    G = (s OR F2) AND (not s OR F3)

is a CNF encoding of their disjunction. Guard a ternary clause (a OR b OR c) with two clauses `(g OR a OR h)` and `(not h OR b OR c)` and a private helper h; shorter clauses need no helper. The solver receives only signed, permuted raw width-three clauses, without the selector, arm boundaries, graphs, or arithmetic labels.

On the recorded controls the unconditioned discovery pass profiles every proposed local scope and finds **zero integer laws**. Under one selector value it refutes one flow using the discovered modulus 2 or 3. It therefore learns the opposite value, then refutes the other flow. Every negative control takes three oracle calls (the initial inconclusive call and the two successful conditional calls), with one learned unit. Positive siblings have a supplied witness lifted through the guard encoding and checked against every original clause; the incomplete oracle correctly reports UNKNOWN under the stated cap.

These are small explicit controls inspired by the disjunction obstruction discussed in [the prior-work review](global_integer_theory.md). They are not the paper's 7-element Maltsev template or a reproduction of its hierarchy theorem.

## Why singleton probing is not the new universal strategy

The same Hall-expansion condition used in [the integer blindness theorem](global_integer_theory.md) defeats singleton probing **before any unit can be learned**. After pinning s=b, for each other coordinate i a matching avoiding both s and i produces local models differing by exactly that coordinate. The integer affine hull contains all integer values for every unpinned coordinate; the only possible new equality is the already assumed value of s. Both sides' global integer relaxations remain consistent. The fixed-locality NP-complete class and the stated linear-locality existential twins therefore also obstruct this fixed point when its oracle uses just those raw local tables. Arbitrary preprocessing that changes the representation is outside that theorem.

The positive experiment checks a useful compositional inference rule. It does not rescue local affine information as a complete representation of arbitrary SAT. Increasing the probe budget on a proved blind family is not the next research target.

## Formal scope

[IntegerCertificate.lean](../Formal/IntegerCertificate.lean) proves the semantic arbitrary-modulus weighted-sum rule and the facts that refuting one value forces the other and refuting both values excludes a model. The Python restriction evaluator, private-resolution implementation, integer discovery, complexity bounds, and the expansion proof are not fully formalized by that file.
