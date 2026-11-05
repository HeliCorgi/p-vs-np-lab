# Ordinary polynomial-calculus formalization

This is a separate Lean package for the phase-21/22/23/24 formalization. The repository's
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

**Latest verified status:** the full package and all **126 theorem axiom audits**
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

The phase-23 composed theorem derives the numerical image bounds from the
original clause ranks and constructs its affine charts and coverage internally.
Its sum is over nonempty discarded node occurrences. Ordinary-PC separation
remains an explicit hypothesis; distinct-flat deduplication, the expander
separator, and quantitative existence/counting are not yet connected as a
complete formal exponential theorem. The
[current scope note](../docs/optimal_affine_parameters.md) records the exact
boundary. The coordinates use classical basis choice, with no executable
elimination claim. No P vs NP claim follows from this package.
