# Phase 22: actual Boolean restriction maps and their dimension budgets

**Verified, 2026-11-06 JST.** Four new Lean modules connect the source affine
clause DAG to concrete restriction maps and the explicit binomial image bound.
The package built on its first hosted attempt at
[`ab108e6`](https://github.com/HeliCorgi/p-vs-np-lab/commit/ab108e6b1077cdae6b4879768c573c682326d3ee).
All **68 named theorem axiom audits**, including 30 new endpoints, passed in
[CI run 42111933039](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42111933039).
The [observed source and axiom record](../results/boolean_restriction_formal_audit.json)
preserves that evidence. P versus NP and full formalization of the phase-20
exponential lower bound remain unfinished.

## 1. The connected theorem now proves its numerical image bounds

Let `V` be a finite set of original variables, and let `F` contain explicit
Boolean axioms. A finite source DAG ends with the constant polynomial `1`.
Each step is an actual input in `F` or a sound unary/binary semantic inference
from strictly earlier nodes. Earlier parents may be reused arbitrarily.
Retain some nodes, with each retained polynomial having ordinary degree at
most `R`. Let `U` be a subspace of ordinary F2 polynomials of degree at most `k`.

For a finite index set `A`, supply nonnegative parameter counts `t_a` and
ordinary affine coordinate polynomials

\[
       g_{a,v}\in\mathbb F_2[y_1,\ldots,y_{t_a}],
       \qquad \deg g_{a,v}\le1.
\]

They define concrete maps

\[
 \Phi_a:\mathbb F_2^{t_a}\longrightarrow\mathbb F_2^V,
 \qquad \Phi_a(y)_v=g_{a,v}(y).
\]

The cover hypothesis says that **every point where a discarded node's
polynomial is nonzero lies in at least one image of a map `Phi_a`**.
The parameterizations may be noninjective, their images may overlap, and they
may cover additional points. Then the formal theorem proves

\[
 \boxed{\dim U\le\dim\bigl(U\cap C_{k+3R}(F)\bigr)
                   +\sum_{a\in A}b_k(t_a)},
 \qquad b_k(t)=\sum_{j=0}^{\min(k,t)}\binom tj.
\]

Here `C_D(F)` is the actual ordinary-PC derivable subspace through degree `D`.
If `U` is separated from that subspace, the intersection term is zero. Both
versions are in
[`ParametrizedDAGDimension.lean`](../formal_pc/ProofLab/ParametrizedDAGDimension.lean).

The actual restriction maps, the meanings of their kernels, their numerical
image bounds, and the kernel-to-PC derivation are proved in the formal chain.
The parameterizations, their coverage, and ordinary-PC separation are still
explicit data or hypotheses. There is no hidden conclusion about the intrinsic
dimension of a clause zero-flat.

## 2. Constructing the restriction map

[`AffineRestriction.lean`](../formal_pc/ProofLab/AffineRestriction.lean) first
constructs ordinary substitution by the coordinate polynomials. It proves

\[
 \deg\bigl(p(g_{a,v})_{v\in V}\bigr)\le\deg p
\]

by expanding an ordinary polynomial into monomials and bounding the degree of
each substituted product. This happens before any Boolean reduction. It then
proves the evaluation identity

\[
 p(g_{a,v})(y)=p(\Phi_a(y)).
\]

The restriction is a genuine linear map into functions on the parameter cube:

\[
 L_a:U\longrightarrow
       \bigl(\mathbb F_2^{t_a}\longrightarrow\mathbb F_2\bigr),
 \qquad L_a(p)(y)=p(\Phi_a(y)).
\]

Its kernel is proved to be exactly pointwise vanishing on the image of `Phi_a`.
Consequently, a polynomial in the joint kernel vanishes on all discarded
nonzero loci, by the stated cover hypothesis. The phase-21 masked replay
therefore derives it in ordinary PC through degree `k+3R`.

No theorem here requires injectivity of `Phi_a`. Extra covered points only
strengthen the vanishing condition; redundant parameters can make the numerical
upper bound weaker. The term `t_a` always denotes a supplied parameter count.

## 3. Proving the truncated binomial budget

[`BooleanFunctionSpace.lean`](../formal_pc/ProofLab/BooleanFunctionSpace.lean)
constructs a linear evaluation map from ordinary polynomials to actual Boolean
functions. The low-degree function space is the span of the functions

\[
                         y\longmapsto\prod_{i\in S}y_i,
                  \qquad |S|\le k.
\]

The pinned Boolean-reduction theorem supplies an explicit squarefree expansion
with the same evaluation as the original polynomial. Every support in that
expansion has cardinality at most the original ordinary total degree. Thus a
degree-at-most-`k` polynomial evaluates into the stated function space.

The allowed supports are partitioned into disjoint layers by cardinality. The
proof establishes their exact count

\[
 \left|\{S\subseteq\{1,\ldots,t\}:|S|\le k\}\right|
       =\sum_{j=0}^{\min(k,t)}\binom tj.
\]

A finite spanning-family dimension bound then proves

\[
              \dim(\operatorname{range}L_a)\le b_k(t_a).
\]

No independence assertion is needed for this upper bound. The theorem covers
`k=0`, zero parameter variables, and `k` greater than the parameter count.

The ordinary polynomial and Boolean-function spaces remain distinct. For
example, `y^2-y` is a nonzero ordinary polynomial and evaluates to zero on the
Boolean cube. The proof first controls ordinary substitution degree and then
uses the checked Boolean evaluation/reduction identity. It does not assign a
squarefree dimension to the unreduced ordinary-polynomial substitution space.

## 4. Connecting the original affine clauses

[`AffineClauseDAG.lean`](../formal_pc/ProofLab/AffineClauseDAG.lean) supplies the
source adapter that was left explicit in phase 21. Its certificate consists of
finite clauses, Boolean input-node tags, and clause-level semantic steps with
strictly earlier parents. An input step must have its raw falsity polynomial
in the actual original axiom set `F`.

The polynomial representation uses raw products on tagged input nodes and the
proved basis-compressed products on derived nodes. The adapter proves that
both representations have the same Boolean values as their source clause,
constructs the sound polynomial DAG, and turns the empty source clause into
the literal ordinary polynomial `1`.

For the degree bound it assumes raw width at most `R` for **all tagged input
nodes**, including discarded ones, and span rank at most `R` for retained
derived nodes. This is slightly stronger than what the general polynomial-DAG
replay needs, and it is stated explicitly. Every clause is affine in the
original variables. The source adapter does not add new extension variables.

The composed clause-level theorem requires only the stated cover of discarded
clauses' common zero-sets. It constructs the polynomial DAG and the restriction
maps itself, then proves the displayed numerical inequality. Empty zero-sets
require no coverage. A zero-parameter cube is still a singleton, so it must
not be confused with an empty zero-set.

## 5. Scope audit and remaining obligation

A focused internal statement audit checked the coverage direction, finite-type
assumptions, raw input membership, explicit Boolean axioms, and the lack of a
hidden final-derivability or image-dimension hypothesis. It found no mathematical
statement defect. This is not external specialist review of the complete
exponential theorem.

| Connection | Current formal status |
|---|---|
| Raw affine-clause DAG to ordinary polynomial DAG | Proved. |
| Actual restriction map and pointwise meaning of its kernel | Proved. |
| Ordinary affine substitution preserves the total-degree bound | Proved. |
| Restriction-image dimension is at most `b_k(t)` for supplied affine coordinates | Proved. |
| Combined ordinary-PC dimension inequality with these concrete maps | Proved. |
| An arbitrary consistent clause has an optimal parameterization with `t = n - spanRank(C)` | Not yet formalized. |
| Empty-support monomials form the required expander-separated space | Paper proof using the published reduction interface; not fully formalized. |
| Quantitative formula existence and final exponential bound | Paper proof; not fully formalized. |

The next acceptance test is one precise existence theorem. For an affine
clause `C` with nonempty common zero-set, write `n = card V` and
`r = spanRank C`. Prove `r ≤ n`, construct degree-at-most-one coordinate
polynomials on `n-r` parameters, and prove that their coordinate map is a
bijection onto the clause's common zero-set. Inconsistent clauses must instead
be shown to have empty zero-sets.

One proof route is to choose a common zero `a`, show that taking linear
coefficients is injective on the affine-form span vanishing at `a`, apply
rank-nullity to the corresponding linear system, and choose coordinates on
its kernel. This is a proposed formalization route, not a theorem supplied by
the current package. Once completed, it connects a high-rank clause to a
parameter count at most `n-R-1` without assuming that correspondence.

The separated-space and counting/existence arguments remain separate work.
Neither this dimension criterion nor the earlier proof-system lower bound
establishes a lower bound on all SAT algorithms.

## 6. Reproduction and provenance

The Lean and Mathlib revisions and the three MIT foundation files are unchanged
from phase 21. No new upstream source files were vendored. The four new modules
add 30 audited endpoints; the package now audits 68 in total. The original core
package separately audits 93 endpoints.

```sh
python3 formal_pc/audit.py --verify-snapshot-only
cd formal_pc
lake exe cache get
lake build ProofLab
python3 audit.py
```

Only `propext`, `Classical.choice`, and `Quot.sound` were observed in the actual
transitive axiom sets. Cached dependencies may be reused; no independent replay
of every cached kernel object is claimed. There were no failed Lean build
checkpoints in this phase. Source declarations and complete theorem statements
remain inspectable in the repository.

Python reproduction still checks 388 tests and 62 deterministic reports. This
cycle adds general formal proofs rather than additional finite benchmarks. The
new formal-audit JSON records observed CI evidence and is not counted as another
deterministic experimental report. The phase-21 audit JSON is retained as a
historical record of its exact pinned source commit.
