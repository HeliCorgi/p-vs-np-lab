# Phase 28: resolution miter as a falsification gate for affine-cover charging

Date: 2026-11-09 JST. Starting main: `31b57fbb56e05fc5edd45111c6680871f66aa2b2`. At preregistration no open PRs; the latest main research-check and ordinary-PC workflows were successful. Phase 27 documented a width-4 OBDD for a satisfiable positive inner-product Tseitin relation. This new gate **does not** rerun its affine-flat enumeration or OBDD residual search.

## Preregistered hypothesis, falsifiers, budget, stop

**H1.** Let `F_m^+` and `F_m^-` be two separately named AND/XOR Tseitin circuits sharing exactly the same `2m` original `x,y` inputs, with opposite required final output bits. Their conjunction `M_m` is an unsatisfiable 3-CNF on `6m-2` variables and `14m-6` input clauses. An ordinary *resolution* refutation (no weakening, extension, XOR or semantic inference rules) exists using at most `18m-12` derived lines, width at most three, with a uniform exact two-parent/pivot certificate.

**H2.** The positive half `F_m^+` retains affine one-cover number `2^m-1` from Phase 26; thus this explicit adversarial miter falsifies any *unqualified* transfer principle claiming that an exponential affine cover of a satisfiable witness half forces an exponential resolution refutation of a corresponding opposite-output double-copy miter.

**Falsifiers.** Any malformed input clause or variable collision, a bad ordinary-resolvent line, a nonempty final clause, an invalid line bound/width, failure of the output-polarity semantics, or a satisfiable opposite-output miter. A claimed lower bound on *other* hard formula families or other proof systems is not falsified.

**Hard stop.** Check the constructed proof at m=1,2,3,7,16 using a separately written, syntax-only ordinary-resolution checker; only brute-force miter truth tables at m=1,2 (maximum 2^10=1024 assignments, below the prior 2048-assignment cap). Check a satisfiable sibling with aligned outputs as a negative control. Do not raise the previous affine-flat search limit, rerun heavy external formalizations, or introduce unbounded proof search. Stop the hypothesis if any checker detects a malformed line rather than changing the claim silently.

**Source and evidence boundary.** Proof-complexity framework: S. Cook and R. Reckhow, *The relative efficiency of propositional proof systems*, JSL 44 (1979) 36–50, https://doi.org/10.2307/2273702 . Tseitin's foundational derivation work: G. S. Tseitin, *On the Complexity of Derivation in Propositional Calculus* (1968; English collection 1983), https://doi.org/10.1007/978-3-642-81955-1_28 . The concrete miter proof template, exact line count, and tests are original deductions for this selected encoding, with no priority claim.

## Outcome

To be completed only after the independent certificate and semantic gates. No P=NP or P≠NP result is claimed, and a future Lean audit of other modules does not formally verify this new resolution theorem.
