# Ordinary polynomial-calculus formalization

This is a separate Lean package for the phase-21/22/23/24/27 formalization and
the phase-20 completion work. The repository's
original `Formal` package remains on Lean 4.19.0. This package pins Lean
4.34.0-rc2 and Mathlib `67248ba34806c60bf24b5e99f0f09946ffc465c9`.

The objects are ordinary `MvPolynomial` polynomials over a field, with a primitive
degree-bounded PC derivation relation. Boolean identities are derived from the
explicit axioms `X v ^ 2 - X v`; they are not treated as cost-free quotient
equalities. Static Nullstellensatz inclusion in PC is one-way.

## Attribution and source integrity

The three files in `claims/` are unmodified software by **Kamil Braun**, from
**Noemesis: A Framework for Autonomous Mathematical Research**, repository
[`kbr-/math-research`](https://github.com/kbr-/math-research), pinned at commit
[`25239211058ef718402a908b3272f01480c159c4`](https://github.com/kbr-/math-research/tree/25239211058ef718402a908b3272f01480c159c4).
They are reused under the **MIT License**. The upstream license and MIT text are
preserved in `third_party/noemesis/`; the manifest records source paths, bytes,
Git blob hashes, and SHA-256 hashes. `ProofLab/` and the package infrastructure are
this lab's additions. Individual files credit any related upstream argument.

This selective reuse does not validate the upstream paper's main theorem or all
of its formalization. No upstream installation script or workflow is executed.

## Verification

```sh
python3 formal_pc/audit.py --verify-snapshot-only
cd formal_pc
lake exe cache get
lake build ProofLab
python3 audit.py
```

The CI job has a 20-minute ceiling and uses the standard Mathlib cache. The final
audit queries the actual transitive axiom dependencies of every named theorem
in `audit_theorems.json` and allows only `propext`, `Classical.choice`, and
`Quot.sound`. It rejects proof holes and nonstandard native-evaluation axioms in
those dependencies. It does not claim an independent Lean-kernel replay of all
cached Mathlib dependencies.

**Latest local status (2026-11-08 JST):** the full package and all **390 theorem
axiom audits** passed. The 70 newly audited theorems close the CNF-family
existence and numerical specialization. For every
`n ≥ 16 * 1024 * 12288^4 * 10^16`,
[`Phase20.exists_unsat_exponential_lower_bound`](ProofLab/Phase20.lean)
constructs an UNSAT proper linear 3-CNF with exactly `12n` clauses, maximum
occurrence 4096, and the required expansion. Every refuting original-variable
affine-clause source DAG has at least
`(1/4) * exp(n / (81 * 2^65 * 10^32))` nodes and distinct nonempty high-rank
false flats. Existence, separation, density, rounding and binomial estimates
are proved inside the chain. See the [precise scope](../docs/phase20_formalization.md)
and [source-bound audit](../results/phase20_complete_formal_audit.json).
This completes the stated phase-20 F2 exponential theorem locally; external
review, novelty assessment and any P versus NP conclusion are separate matters.

**Previous local status:** 320 theorem axiom audits passed for connected
obstruction counting, positive association, binomial tails and good-set density.
The [density record](../results/phase20_density_formal_audit.json) retains its
original source hashes and then-outstanding family/exponent obligations.

**Previous local status:** 245 theorem axiom audits passed for constructed ideal
normal forms, the expander reduction operator, and ordinary-PC separation for
every signing. The [separator record](../results/phase20_separator_formal_audit.json)
retains its original source hashes and then-outstanding density obligation.

**Previous local status:** 181 theorem axiom audits passed for distinct-flat
counting, pooled-support size and absorption, local satisfiability, and exact
good-monomial dimension. The [earlier record](../results/phase20_formal_progress_audit.json)
retains its original source hashes and then-outstanding separation obligation.

**Previous local status:** the full package and all **142 theorem axiom audits**
passed for the phase-27 working tree. The [local audit record](../results/extension_substitution_formal_audit.json)
contains source hashes and actual axiom sets. The 16 new endpoints prove
ordinary-PC degree transfer under polynomial substitution, Boolean extension
corollaries, and the sharp AND-coordinate obstruction. This is local
verification, not a new GitHub CI run. See [the exact scope](../docs/extension_substitution.md).

**Previous hosted status:** the full package and all **126 theorem axiom audits**
passed in [CI run 42125609896](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42125609896)
at source commit `6aa1b3feccd9476a2ef8209b16d22b1a6968e3b5`. The
[phase-24 audit record](../results/affine_cover_formal_audit.json) preserves exact
source hashes, all observed axiom sets, and the failed continuation checkpoints.
The two additional modules prove the inner-product polar-rank bound and an
exponential affine one-cover lower bound. Their
[scope note](../docs/affine_cover_circuit_boundary.md) explains why this does
not extend the earlier theorem to arbitrary Boolean computations.

The phase-23 package and all **106 theorem axiom audits** passed
in [CI run 42116967349](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42116967349)
at source commit `e8bf0ee8c074583ce10df180849153f418847189`. The exact source hashes
and observed axiom sets are preserved in the
[phase-23 audit record](../results/optimal_affine_formal_audit.json).
The [68-endpoint phase-22 record](../results/boolean_restriction_formal_audit.json)
and [38-endpoint phase-21 record](../results/ordinary_pc_formal_audit.json) are
retained as historical evidence for their exact source commits.

| Module | Verified mathematical content |
|---|---|
| [ProofLab.DistinctAffineFlats](ProofLab/DistinctAffineFlats.lean) | Deduplication by actual zero-sets, rank invariance under equal nonempty zero-sets, distinct-flat dimension and cardinality budgets, and source line counts. Ordinary-PC separation remains a hypothesis. |
| [ProofLab.ExpanderSupport](ProofLab/ExpanderSupport.lean) | Actual finite boundaries and pooled supports, a size bound for the whole union, and the support-absorption lemma needed by the reduction operator. |
| [ProofLab.ExpanderLocalConsistency](ProofLab/ExpanderLocalConsistency.lean) | Private-variable peeling gives local satisfying assignments for every signing, connected to the existing raw ordinary clause polynomials. |
| [ProofLab.ExpanderMonomials](ProofLab/ExpanderMonomials.lean) | The actual empty-support monomial space, exact dimension, degree bound, and its conditional connection to distinct DAG flats. This does not construct the separating operator. |
| [ProofLab.IdealNormalForm](ProofLab/IdealNormalForm.lean) | Constructed ideal normal forms: existence, uniqueness, linearity, exact kernel, degree bound, and multiplication after ideal enlargement. |
| [ProofLab.BooleanIdealNormalForm](ProofLab/BooleanIdealNormalForm.lean) | Explicit Boolean generators force multilinearity; Boolean normalization fixes squarefree polynomials; signed raw clauses define the local ideals. |
| [ProofLab.NormalFormRestriction](ProofLab/NormalFormRestriction.lean) | Pinning a variable preserves standardness and compares normal forms across ideals. |
| [ProofLab.ExpanderNormalForm](ProofLab/ExpanderNormalForm.lean) | Private-variable elimination proves support-enlargement consistency and the neighborhood bound for actual normal forms. |
| [ProofLab.ExpanderReduction](ProofLab/ExpanderReduction.lean) | The actual linear operator fixes the good space, kills all degree-B PC derivations, and proves separation from expansion for every signing. Multiplication includes repeated variables. |
| [ProofLab.ExpanderDAGLowerBound](ProofLab/ExpanderDAGLowerBound.lean) | Distinct-flat and source-line budgets for the actual signed source family, with separation proved internally. The density specialization is supplied by `ExpanderDensityDAG`. |
| [ProofLab.FiniteBernoulli](ProofLab/FiniteBernoulli.lean) | Explicit finite product weights, normalization, exact containment probabilities, positive association for overlapping decreasing events, and uniform-layer cardinalities. |
| [ProofLab.BernoulliBounds](ProofLab/BernoulliBounds.lean) | Exponential avoidance bounds, generating functions and moments, direct Markov estimates, two-sided binomial tails, and dense central-layer selection. |
| [ProofLab.ConnectedSetCounting](ProofLab/ConnectedSetCounting.lean) | A constructed closed tour of length 2(t−1) for every connected t-set, and the bounded-degree connected-set count. |
| [ProofLab.ExpanderObstructions](ProofLab/ExpanderObstructions.lean) | Empty pooled support exactly equals avoidance of connected boundaries; the actual intersection graph inherits the occurrence bound. |
| [ProofLab.LinearClauseBoundary](ProofLab/LinearClauseBoundary.lean) | Incidence counting in linear triples yields boundary size at least three; expansion supplies the size-dependent bound. |
| [ProofLab.BoundaryProbabilitySum](ProofLab/BoundaryProbabilitySum.lean) | The explicit sum of connected obstruction probabilities is at most 7mC⁴p³, including the finite geometric-series calculation. |
| [ProofLab.ExpanderDensity](ProofLab/ExpanderDensity.lean) | The actual good-set density is at least ½ exp(−168nC⁴p³) times binomial(n,k) for some pn/2 ≤ k ≤ 2pn under the stated structural and numerical conditions. |
| [ProofLab.ExpanderDensityDAG](ProofLab/ExpanderDensityDAG.lean) | The selected degree works for every signing and applicable DAG, with both separation and quantitative density proved internally. |
| [ProofLab.ExtensionSubstitution](ProofLab/ExtensionSubstitution.lean) | Substitution of degree-B ordinary PC through degree DB, all-cube Boolean definitions, and sharp degree/replay costs for AND coordinates. No general circuit or proof-size lower bound is claimed. |
| `ProofLab.MaskedDAG` | Actual ordinary-PC replay at degree `k+3R`, with arbitrary reuse of earlier parents and explicit Boolean corrections. |
| `ProofLab.AffineIndicators` | Concrete affine-clause products, extracted basis subclauses, compressed semantics/degree, actual raw-input compression, and exact CNF products. |
| `ProofLab.DimensionBudget` | Joint-kernel dimension bounds with finite-dimensional source spaces, allowing infinite-dimensional ambient spaces and restriction codomains. |
| `ProofLab.DAGDimension` | The composed theorem derives kernel-to-PC containment internally from a semantic DAG, then applies the dimension bound. |
| `ProofLab.BooleanFunctionSpace` | Actual Boolean function evaluation, squarefree spanning supports, their exact truncated-binomial count, and the function-space dimension upper bound. |
| `ProofLab.AffineRestriction` | Actual affine-coordinate restriction maps, their pointwise kernels, ordinary substitution degree, and the proved numerical image bound. |
| `ProofLab.AffineClauseDAG` | Raw source clause products and compressed derived clauses construct a sound polynomial DAG with the stated retained degree bound. |
| `ProofLab.ParametrizedDAGDimension` | Concrete affine covers supply all numerical image budgets internally, yielding the dimension criterion directly for polynomial or affine-clause DAGs. |
| `ProofLab.AffineCoefficients` | Ordinary affine coefficient reconstruction, evaluation under translation, and rank-preserving slope projection on a consistent affine span. |
| `ProofLab.DualKernelCoordinates` | Common-kernel dimension and exact linear coordinates for any finite-dimensional vector space over any field. |
| `ProofLab.OptimalAffineParameters` | An actual injective affine map with exactly `n-spanRank C` parameters, exact clause-zero image, and degree-at-most-one coordinate-polynomial encoding. |
| `ProofLab.IntrinsicAffineRestriction` | Exact vanishing kernel, intrinsic Boolean image budget, high-rank parameter bound, and a source-DAG criterion constructing all charts and coverage internally. |
| `ProofLab.QuadraticPolar` | Explicit nondegenerate polar pairing of the binary inner product, isotropic constant-flat directions, and the derived dimension bound for injective affine charts. |
| `ProofLab.QuadraticAffineCover` | An explicit large subset of the positive level, finite-union counting with overlaps, and an exponential lower bound on the number of covering affine charts. |
| [ProofLab.CNFFamilyExistence](ProofLab/CNFFamilyExistence.lean) | Actual finite random triples, simultaneous expansion/count/degree/collision estimates, deletion preserving exactly 12n clauses, bounded occurrence, and UNSAT/SAT signings. |
| [ProofLab.ExponentialBudget](ProofLab/ExponentialBudget.lean) | Truncated binomial sums, exponential binomial ratios, integer rounding and the exact numerical exponent. |
| [ProofLab.Phase20](ProofLab/Phase20.lean) | The complete existential F2 exponential theorem, with an explicit ambient-size threshold and no unproved family, separator or density premise. |

The phase-23 theorem constructs affine charts and coverage internally and sums
over nonempty discarded node occurrences. The new `DistinctAffineFlats` theorem
deduplicates those sets semantically and proves the uniform count bound.
The generic distinct-flat theorem retains a separation hypothesis;
`ExpanderDAGLowerBound` discharges it for the actual signed raw-clause family.
`ExpanderDensityDAG` additionally discharges the quantitative density condition.
`CNFFamilyExistence` constructs the required family and UNSAT signing;
`ExponentialBudget` proves the final numerical inequalities, and `Phase20`
composes their existence and exponential conclusion. The
[current scope note](../docs/phase20_formalization.md)
states the complete theorem and its explicit threshold. The coordinates and representatives use
classical choice, as do the normal forms; no efficient computation is claimed. No P vs NP claim follows
from this package.
