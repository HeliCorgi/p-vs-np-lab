# Phase 23: optimal affine coordinates for every nonempty clause zero-set

**Verified, 2026-11-06 JST.** The exact chart theorem and its connected
restriction/DAG corollaries passed the complete hosted Lean build at
[`e8bf0ee`](https://github.com/HeliCorgi/p-vs-np-lab/commit/e8bf0ee8c074583ce10df180849153f418847189).
All **106 named theorem axiom audits**, including 38 new endpoints, passed in
[CI run 42116967349](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42116967349).
The [observed source and axiom record](../results/optimal_affine_formal_audit.json)
preserves that evidence. The selected phase-22 acceptance test is completed;
the expander separator and full exponential theorem remain separate obligations.

## 1. Exact theorem and its meaning

Let `V` be any finite type of original Boolean variables, let `n = card V`,
and let `C` be a finite clause of ordinary polynomials over `F2`, each of total
degree at most one. Its falsifying assignments are the common zero-set

\[
 Z(C)=\{x\in\mathbb F_2^V:\forall p\in C,\ p(x)=0\}.
\]

The existing definition retains constants when taking the polynomial span:

\[
 r=\operatorname{spanRank}(C)
   =\dim_{\mathbb F_2}\operatorname{span}(C)
   \quad\text{inside }\mathbb F_2[X_v:v\in V].
\]

If `Z(C)` is nonempty, the new theorem derives `r <= n` and constructs an
affine map

\[
 \boxed{\Phi_C:\mathbb F_2^{\,n-r}\longrightarrow\mathbb F_2^V,
        \qquad \operatorname{image}\Phi_C=Z(C),\quad
        \Phi_C\text{ injective}.}
\]

Thus every falsifying assignment has exactly one parameter vector. The theorem
also constructs ordinary coordinate polynomials `g_v` of total degree at most
one and proves `Phi_C(y)_v = eval y g_v`. The map is an actual bundled Lean
`AffineMap`, and the polynomial encoding is proved to be its underlying
function. Neither a coordinate chart nor the desired dimension formula is
assumed.

The principal endpoints in
[`OptimalAffineParameters.lean`](../formal_pc/ProofLab/OptimalAffineParameters.lean)
are `spanRank_le_card_variables`, `exists_optimal_parameterization`, and
`exists_optimal_affineMap`. The polynomial-facing existence statement is:

```lean
theorem exists_optimal_parameterization
    (C : Clause V) (hC : IsAffineClause C)
    (hne : ∃ a, clauseZero C a) :
    ∃ g : V → Poly (Fin (Fintype.card V - spanRank C)),
      (∀ v, (g v).totalDegree ≤ 1) ∧
      Function.Injective (AffineRestriction.coordinateMap g) ∧
      ∀ x, (∃ y, AffineRestriction.coordinateMap g y = x) ↔
        clauseZero C x
```

The only variable-type assumption is `[Fintype V]`; the zero-variable case is
included. Choices of anchors and bases are classical. This is a mathematical
construction, not a newly implemented Gaussian-elimination program or a
claimed all-input polynomial-time SAT algorithm.

## 2. Why the existing polynomial rank is the right rank

The subtle point is that `spanRank` includes constant coefficients. Merely
discarding those coefficients need not preserve rank for arbitrary clauses.
Consistency supplies the necessary injectivity argument.

First, for any ordinary polynomial `p` with total degree at most one,
[`AffineCoefficients.lean`](../formal_pc/ProofLab/AffineCoefficients.lean) proves
the polynomial identity

\[
 p=p_0+\sum_{v\in V}p_vX_v,
 \qquad p_0=\operatorname{coeff}_0(p),\quad
 p_v=\operatorname{coeff}_{X_v}(p).
\]

This is coefficient equality in the ordinary polynomial ring, not just equality
of Boolean functions. Define the slope functional and its induced linear map by

\[
 \lambda_p(x)=\sum_vp_vx_v,
 \qquad \Lambda:p\longmapsto\lambda_p.
\]

Choose a common zero `a`. Every `p` in `span(C)` still has degree at most one
and vanishes at `a`. If `Lambda(p)=0`, then all linear coefficients are zero;
the affine reconstruction makes `p` constant, and `p(a)=0` makes that constant
zero. Therefore `Lambda` is injective on `span(C)`. Its actual image `S` in the
dual assignment space has dimension exactly `r`:

\[
 S=\Lambda(\operatorname{span}(C)),\qquad \dim S=r.
\]

The module also proves the translation identity

\[
                  p(a+z)=p(a)+\lambda_p(z).
\]

These results connect the original polynomial definition to linear constraints
without changing the meaning of rank or assuming that the infinite-dimensional
ordinary-polynomial ambient space is finite dimensional.

## 3. Common-kernel dimension and the concrete chart

Let

\[
 D=\{z\in\mathbb F_2^V:\forall\lambda\in S,\ \lambda(z)=0\}.
\]

[`DualKernelCoordinates.lean`](../formal_pc/ProofLab/DualKernelCoordinates.lean)
derives `dim S + dim D = dim E` for any finite-dimensional vector space `E`
over any field, using the pinned Mathlib coannihilator theorem. Consequently,
`dim S <= dim E` and `dim D = dim E - dim S`; natural subtraction is justified
by the proved rank bound. The module constructs a linear equivalence from a
coordinate space of that exact dimension onto `D`. It covers zero dimensions
and does not require a finite field.

For the affine clause, the translation identity gives

\[
                 x\in Z(C)\quad\Longleftrightarrow\quad x-a\in D.
\]

Hence `dim D = n-r`. Choose a linear equivalence
`e : F2^(n-r) ≃ D`. The required map is

\[
                         \Phi_C(y)=a+e(y).
\]

Injectivity follows from injectivity of `e` and cancellation of the translation.
For any `x` in `Z(C)`, the inverse coordinates of `x-a` give a preimage. Every
output satisfies all clause equations by the definition of `D`. This proves
exact image and uniqueness, not just coverage.

Writing `epsilon_j` for the standard basis vectors, the constructed ordinary
coordinate polynomial is

\[
       g_v(Y)=a_v+\sum_{j=1}^{n-r}(e(\epsilon_j))_vY_j.
\]

The proof expands an actual linear map on the standard basis and proves that
evaluation of these polynomials equals `a+e(y)`. The ordinary degree bound is
inherited from the previously checked `affinePolynomial_degree` theorem.

This is standard finite-dimensional affine linear algebra. The research
contribution here is the checked connection between the repository's exact
ordinary-polynomial rank, concrete affine charts, restriction maps, and PC
replay. No new linear-algebra theorem or P versus NP breakthrough is claimed.

## 4. Edge cases and a small illustration

| Case | What the theorem supplies |
|---|---|
| `C` empty, or all its forms zero | Rank zero; a chart of the entire assignment space with `n` parameters. |
| Redundant equations in `C` | Only their span rank counts; no parameter is removed twice. |
| Consistent rank `n` | A zero-parameter cube, which is a singleton, representing the unique common zero. |
| No original variables | The statement still includes the unique empty assignment whenever the equations are consistent. |
| Empty common zero-set | The nonemptiness hypothesis fails; no chart from a parameter cube is asserted. |

For example, over `F2` take four variables and

\[
 C=\{X_1+X_2+1,\ X_2+X_3,\ X_1+X_3+1\}.
\]

The third form is the sum of the first two, so `r=2`, although the clause has
three forms. Its common zero-set is represented exactly once by

\[
                    (s,t)\longmapsto(1+s,s,s,t).
\]

This illustration explains the theorem; it is not evidence for the general
proof. The general Lean theorem quantifies over every finite variable type
and every consistent affine clause.

The nonemptiness condition is essential. A clause containing the constant form
`1` has no common zero. In particular, `n-r=0` must never be interpreted as an
empty parameter space: `Fin 0 → F2` has one element.

## 5. Connection to restriction dimensions and the source DAG

[`IntrinsicAffineRestriction.lean`](../formal_pc/ProofLab/IntrinsicAffineRestriction.lean)
chooses the proved chart and constructs its actual restriction on a polynomial
subspace `U`:

\[
 L_C(p)(y)=p(\Phi_C(y)).
\]

It proves both the exact kernel identity and the intrinsic image budget:

\[
 \ker L_C=\{p\in U:p|_{Z(C)}=0\},\qquad
 \dim\operatorname{range}L_C\le b_k(n-r),
 \quad b_k(t)=\sum_{j=0}^{\min(k,t)}\binom tj,
\]

provided all polynomials in `U` have ordinary degree at most `k`. The second
statement uses the phase-22 Boolean-function theorem; it does not mistake the
unreduced ordinary-polynomial space for the smaller Boolean-function space.

The source-clause DAG theorem now constructs every needed chart internally.
Let `A` be the finite set of discarded node occurrences whose common zero-sets
are nonempty. Under the existing Boolean-axiom, source-DAG soundness, input-width,
retained-rank, empty-finish, and degree hypotheses, it proves

\[
 \boxed{\dim U\le\dim\bigl(U\cap C_{k+3R}(F)\bigr)
        +\sum_{i\in A}b_k\bigl(n-\operatorname{spanRank}(C_i)\bigr).}
\]

Here `C_D(F)` is the actual ordinary-PC derivable space through degree `D`.
There is no supplied chart, coverage premise, numerical image-bound premise,
or assumed final PC derivability. The separate ordinary-PC separation premise
eliminates the intersection term. It is still a genuine unproved application
obligation for the intended expander source space.

Empty zero-sets have no index in `A` and contribute no artificial budget of one.
Repeated nodes are counted separately. This new corollary does not yet give the
paper theorem's count of *distinct* flats. The general phase-22 cover theorem
remains available for a suitable family of representatives.

A further checked helper proves, for consistent `C` with `r>R`,

\[
                       R<n,\qquad n-r\le n-R-1.
\]

The DAG theorem permits an arbitrary retention predicate `Low`; it does not
silently infer this strict-rank hypothesis from discard status.

## 6. Verification, provenance, and remaining work

The package pins Lean `4.34.0-rc2` and Mathlib
`67248ba34806c60bf24b5e99f0f09946ffc465c9`. The three previously vendored MIT
foundation files and their licenses are unchanged. No additional upstream
claim files, installers, or workflows were imported. The common-kernel layer
uses Mathlib's primary
[`Dual/Lemmas.lean`](https://github.com/leanprover-community/mathlib4/blob/67248ba34806c60bf24b5e99f0f09946ffc465c9/Mathlib/LinearAlgebra/Dual/Lemmas.lean)
and chosen-basis APIs. The prior upstream finite-affine-coordinate source was
inspected for context; it is not a new vendored dependency.

```sh
python3 formal_pc/audit.py --verify-snapshot-only
cd formal_pc
lake exe cache get
lake build ProofLab
python3 audit.py
```

All 106 named endpoint audits passed, 38 more than phase 22. Only `propext`,
`Classical.choice`, and `Quot.sound` were observed in their actual transitive
axiom sets. Standard cached dependencies may be reused; this is not an
independent replay of every cached kernel object. The original core package
separately audits 93 endpoints. Independent local Python reproduction passed
388 tests and matched all 62 deterministic reports, including current source
hashes. Those numerical checks are separate from formal verification.

The first partial checkpoint compiled the generic dual-kernel module and
exposed one unclosed coefficient-simplification goal: the degree-one monomial
exponent must be explicitly distinguished from the zero exponent. Evaluating
those exponent vectors at the selected variable supplies the contradiction
`0=1` in the natural numbers. The theorem statement and mathematical proof
were unchanged by this elaboration repair. The second checkpoint exposed a
dependent-type simplification failure when transporting the coordinate-space
dimension. Choosing a basis directly from the already proved direction-space
dimension resolved it. Both failed checkpoint IDs and the successful complete
build are recorded in the audit JSON; neither repair weakened the theorem.

An independent internal statement review checked exact image, injectivity,
zero dimensions, the original polynomial-rank definition, all source-DAG
premises, the nonempty-node indexing, and the remaining PC separation premise.
It found no mathematical statement defect. This is not external specialist
review of the full phase-20 exponential argument.

The next substantial application obligation is the expander reduction operator
and separation of an entire polynomial subspace from actual bounded-degree PC.
Individual monomials being nonderivable is insufficient to establish that
subspace statement. Quantitative formula existence, counting, distinct-flat
deduplication in the intrinsic corollary, and the full exponential theorem are
separate from the exact chart theorem completed here. General SAT complexity
and P versus NP are not resolved by this work.
