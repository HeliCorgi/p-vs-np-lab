# Phase 28: resolution miter as a falsification gate for affine-cover charging

Date: 2026-11-09 JST. Starting main: `31b57fbb56e05fc5edd45111c6680871f66aa2b2`. At preregistration no open PRs; the latest main research-check and ordinary-PC workflows were successful. Phase 27 documented a width-4 OBDD for a satisfiable positive inner-product Tseitin relation. This new gate **does not** rerun its affine-flat enumeration or OBDD residual search.

## Preregistered hypothesis, falsifiers, budget, stop

**H1.** Let `F_m^+` and `F_m^-` be two separately named AND/XOR Tseitin circuits sharing exactly the same `2m` original `x,y` inputs, with opposite required final output bits. Their conjunction `M_m` is an unsatisfiable 3-CNF on `6m-2` variables and `14m-6` input clauses. An ordinary *resolution* refutation (no weakening, extension, XOR or semantic inference rules) exists using at most `18m-12` derived lines, width at most three, with a uniform exact two-parent/pivot certificate.

**H2.** The positive half `F_m^+` retains affine one-cover number `2^m-1` from Phase 26; thus this explicit adversarial miter falsifies any *unqualified* transfer principle claiming that an exponential affine cover of a satisfiable witness half forces an exponential resolution refutation of a corresponding opposite-output double-copy miter.

**Falsifiers.** Any malformed input clause or variable collision, a bad ordinary-resolvent line, a nonempty final clause, an invalid line bound/width, failure of the output-polarity semantics, or a satisfiable opposite-output miter. A claimed lower bound on *other* hard formula families or other proof systems is not falsified.

**Hard stop.** Check the constructed proof at m=1,2,3,7,16 using a separately written, syntax-only ordinary-resolution checker; only brute-force miter truth tables at m=1,2 (maximum 2^10=1024 assignments, below the prior 2048-assignment cap). Check a satisfiable sibling with aligned outputs as a negative control. Do not raise the previous affine-flat search limit, rerun heavy external formalizations, or introduce unbounded proof search. Stop the hypothesis if any checker detects a malformed line rather than changing the claim silently.

**Source and evidence boundary.** Proof-complexity framework: S. Cook and R. Reckhow, *The relative efficiency of propositional proof systems*, JSL 44 (1979) 36–50, https://doi.org/10.2307/2273702 . Tseitin's foundational derivation work: G. S. Tseitin, *On the Complexity of Derivation in Propositional Calculus* (1968; English collection 1983), https://doi.org/10.1007/978-3-642-81955-1_28 . The concrete miter proof template, exact line count, and tests are original deductions for this selected encoding, with no priority claim.

## Outcome: exact uniform certificate construction, specific negative transfer

**Mathematical theorem (all m >= 1).** The opposite-output two-copy miter M_m
has 6m-2 variables and 14m-6 input 3-CNF clauses. It has an ordinary
binary-resolution refutation with 18m-12 **derived** clauses, of maximum
width three. Including input clauses, the proof has 32m-18 lines.
This is a constructive upper bound, not a minimum-proof-size claim.

Each circuit uses the same x,y inputs and disjoint AND and XOR auxiliary
variables; one circuit requires inner product output 1 and the other output 0.
Every original assignment uniquely forces each circuit's gate values, giving
equal outputs. Hence the joint miter is unsatisfiable. The two output unit
clauses use **different variables**; there is no trivial pair of opposite
unit clauses in the input.

**Explicit proof template.** For every pair of AND outputs a and b,
derive the implication (-a OR b): resolve (-a OR x) against
(b OR -x OR -y) on x to obtain (-a OR b OR -y); then resolve
against (-a OR y) on -y. Reverse the roles of a and b for
(-b OR a). Exactly four derived clauses per pair.

For a pair of XOR gates with inputs a,b and a',b' and outputs c,c',
assume by induction the two equivalence clauses for a,a' and b,b'.
Resolve each of the four clauses of the second XOR gate with the
appropriate equivalence clauses, replacing both primed input literals
by the unprimed ones. This takes eight resolutions and leaves each
clause of width at most three.

To derive (-c OR c'), combine (a OR b OR -c) with (a OR -b OR c')
on b, and combine (-a OR b OR c') with (-a OR -b OR -c) on b.
The two 3-clause resolvents have opposite a literals; resolve on a to
get (-c OR c'). Exchanging the roles of c and c' gives
(-c' OR c) in three more steps. Thus each XOR adds 8+6=14 lines.
The output equivalence is then available for the next prefix gate.
Finally resolve the first output's positive unit with
(-lastA OR lastB), obtaining (lastB); resolve it against the second
output's negative unit to derive the empty clause. All inference
steps are **ordinary resolution**, with no weakening or extra axioms.

The exact construction counts are

    4m + 14(m-1) + 2 = 18m-12 derived lines,
    (14m-6) + (18m-12) = 32m-18 lines including inputs.

**Falsification.** The Phase 26 positive single-copy witness relation
requires exactly 2^m-1 affine flats, yet the corresponding opposite-output
double-copy miter has the above linear-size ordinary resolution refutation.
For m=16 these numbers are **65,535** affine flats, **276** derived
resolution clauses and **494** proof lines including inputs. Therefore
an unrestricted rule charging this miter's resolution refutation by the
positive half's affine one-cover is false. Other formula families and
additional restrictions on proof systems are not covered.

## Independent finite audit and replay

The deterministic certificate constructor is
[experiments/tseitin_resolution_miter.py](../experiments/tseitin_resolution_miter.py).
Each derived clause names two earlier clause indices, a signed pivot,
and its alleged resolvent; the generator is not trusted by the separate
set-based independent replay in
[tests/test_tseitin_resolution_miter.py](../tests/test_tseitin_resolution_miter.py).
Tests also change pivots, parent references, clauses and input literals
deliberately to ensure that malformed certificates are rejected.

The [fixed report](../results/tseitin_resolution_miter.json) records
SHA-256 digests of the generated certificate and the following numbers:

| m | variables | input clauses | derived lines | total lines | positive one-cover |
|--:|--:|--:|--:|--:|--:|
| 1 | 4 | 8 | 6 | 14 | 1 |
| 2 | 10 | 22 | 24 | 46 | 3 |
| 3 | 16 | 36 | 42 | 78 | 7 |
| 7 | 40 | 92 | 114 | 206 | 127 |
| 16 | 94 | 218 | 276 | 494 | 65,535 |

Only m=1,2 are subjected to exhaustive full extended truth-table
checks: respectively 16 and 1,024 total assignments, no satisfying
miter assignments, and 1 and 6 satisfying assignments for the
*aligned-output sibling*. For all five displayed m, the independent
checker replays every generated resolution inference, and an explicit
satisfying assignment is checked for the aligned-output sibling.
The full truth table is **not** enumerated for m=3,7,16.

Reproduction commands:

    python experiments/tseitin_resolution_miter.py --out-dir reproduced
    python -m unittest discover -s tests -p test_tseitin_resolution_miter.py -v
    python scripts/reproduce.py --out-dir reproduced --check

**Evidence boundary.** The general statement is an explicit mathematical
induction and syntactic certificate scheme. Python checks selected m only.
No new Lean lemma verifies this theorem; passing preexisting Lean CI cannot
be counted as formalization of it. No general P versus NP implication.

## Next falsification

A genuine general proof-complexity lower bound would require a family of
unsatisfiable formulas and a *sound, explicit* simulation or charging
theorem for a precisely fixed inference system, not the positive-one-cover
of a related satisfiable half. The next candidate should first be tested
on this miter and on auxiliary-variable substitution. Avoid increasing
previous brute-force caps without an independent mathematical reason.

