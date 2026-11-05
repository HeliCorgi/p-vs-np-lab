# Ordinary polynomial-calculus formalization

This is a separate Lean package for the phase-21 formalization. The repository's
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

**Verified status:** the full package and all **38 theorem axiom audits** passed
in [CI run 42058417943](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42058417943)
at source commit `14fd320fb6c722d77b1d7db01622c58d48729c41`. The exact source hashes
and observed axiom sets are preserved in the
[audit record](../results/ordinary_pc_formal_audit.json).

| Module | Verified mathematical content |
|---|---|
| `ProofLab.MaskedDAG` | Actual ordinary-PC replay at degree `k+3R`, with arbitrary reuse of earlier parents and explicit Boolean corrections. |
| `ProofLab.AffineIndicators` | Concrete affine-clause products, extracted basis subclauses, compressed semantics/degree, actual raw-input compression, and exact CNF products. |
| `ProofLab.DimensionBudget` | Joint-kernel dimension bounds with finite-dimensional source spaces, allowing infinite-dimensional ambient spaces and restriction codomains. |
| `ProofLab.DAGDimension` | The composed theorem derives kernel-to-PC containment internally from a semantic DAG, then applies the dimension bound. |

The composed theorem still takes numerical image bounds and ordinary-PC
separation as explicit hypotheses. Affine-flat codimension, the squarefree
restriction-image formula, and the expander separator are separate unfinished
obligations. The [full scope note](../docs/ordinary_pc_formalization.md) records
them. No P vs NP claim follows from this package.
