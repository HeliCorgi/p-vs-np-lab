# Phase 21: ordinary-PC replay and the exact remaining geometry

The phase-20 [common-annihilator argument](affine_dag_annihilator.md) now has
an implementation in the separate [`formal_pc`](../formal_pc/README.md) Lean
package. This cycle formalizes actual ordinary polynomials and degree-bounded
PC derivations, not just identities between Boolean values. The full
[exponential lower bound](expander_separated_space.md) still has mathematical
dependencies outside this package. No P versus NP solution is claimed.

**Verified status:** the complete package built successfully at commit
[`14fd320`](https://github.com/HeliCorgi/p-vs-np-lab/commit/14fd320fb6c722d77b1d7db01622c58d48729c41),
and all **38 named theorem axiom audits passed** in
[CI run 42058417943](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42058417943).
The [observed verification record](../results/ordinary_pc_formal_audit.json)
contains exact source hashes and the actual transitive axiom sets. Only
`propext`, `Classical.choice`, and `Quot.sound` were present.

## 1. Objects and the replay theorem

Let `V` be a finite variable type and `F` a set of ordinary polynomials over F2
in those variables, containing the explicit Boolean
axioms `X v ^ 2 - X v`. `Derives F D p` is the primitive inductive PC relation:
zero, an axiom of degree at most `D`, addition, scalar multiplication, and
multiplication by one variable when the resulting ordinary degree is at most
`D`. It does not include a semantic rule or a free multilinear-reduction rule.

A source DAG has a finite topological indexing `Fin S`, ordinary polynomials
`q i`, and one of the following justifications for every node:

- The actual source polynomial belongs to `F`.
- One earlier node semantically implies it on the Boolean cube.
- Two earlier nodes jointly semantically imply it on the Boolean cube.

Zero evaluation denotes satisfaction. All parents have strictly smaller
indices; a parent may be used arbitrarily many times. The finish polynomial
is exactly the ordinary constant `1`. There is no restriction on DAG depth,
regularity, outdegree, or the supports of the polynomials.

Choose any retained-node predicate `Low`. Suppose every retained `q i` has
ordinary degree at most `R`, and a common polynomial `f` has degree at most `k`
and vanishes wherever any discarded `q i` evaluates nonzero. Then

\[
                     F\vdash^{\mathrm{PC}}_{k+3R} f.
\]

This is `BoundaryLab.MaskedDAG.masked_dag_replay`. Its induction proves
`F ⊢_{k+3R} f * q i` for every retained node. It also covers discarded inputs
and a discarded finish: in the latter case `f` vanishes everywhere and the
explicit Boolean axioms derive it. The theorem allows `k=0` and `R=0`.

The algebraic replay layer is more general than affine clauses. Its source
polynomials may be arbitrary F2 polynomials; only the retained degrees and
discarded nonzero loci enter. This generality supplies no automatic geometric
image-dimension bound and no lower bound for all possible proof systems.

### Where the degree goes

For retained parents `a,b` and retained conclusion `c`, the identity is

\[
 c(fa)+(1-a)c(fb)+fc(1-a)(1-b)=fc.
\]

The last term is Boolean-zero by soundness and has ordinary degree at most
`k+3R`. If `a` was discarded, the correction becomes `fc(1-b)`, of degree at
most `k+2R`; soundness and the vanishing of `f` supply the zero evaluation.
No high-degree indicator is inserted into that product. If both parents were
discarded, `fc` itself is Boolean-zero, at degree at most `k+R`.

Each Boolean-zero correction is first given an explicit bounded
Nullstellensatz certificate from the Boolean axioms, then converted to PC.
Only **NS inclusion in PC** is used. The false converse would fail on the
[phase-20 PC-space control](pc_subspace_audit.md).

Multiplying an already completed PC line by a polynomial uses degree
`max(old proof bound, degree multiplier + degree line)`. It does not multiply
every line of the old derivation. Thus the same ceiling works at every depth.
This theorem bounds degree, not the time to discover `f`, the expanded PC
certificate size, or the running time of a SAT algorithm.

## 2. Concrete affine indicators and raw CNF input

[`AffineIndicators.lean`](../formal_pc/ProofLab/AffineIndicators.lean) represents
a finite affine clause by a finite set `C` of actual ordinary polynomials of
degree at most one. Its raw falsity polynomial is

\[
                          q_C=\prod_{g\in C}(1-g).
\]

The module proves that its value is one exactly when every form in `C` is
zero, and zero exactly when the disjunction is true. It extracts a basis
subclause `B ⊆ C` with the same ordinary-polynomial linear span and
`B.card = spanRank C`, then constructs the compressed polynomial `q_B`.
The compressed polynomial has degree at most `spanRank C` and the same Boolean
evaluations as `q_C`. The empty clause gives exactly `1`.

The basis is obtained mathematically using classical choice. No efficient
implemented basis finder or SAT algorithm is being claimed. The module also
constructs affine polynomials from explicit constant and coefficient data,
proves the degree bound, and proves exact equality of the raw clause polynomial
with the usual CNF product of `1-X v` for positive literals and `X v` for
negative literals. Repeated powers remain ordinary powers. Compression of a
raw input has an actual PC derivation through its raw width, using a Boolean
correction rather than treating two Boolean-equivalent polynomials as equal.

For applying the replay theorem, raw input polynomials may be kept on initial
nodes while compressed polynomials are used on derived nodes. Soundness is
transported by equality of evaluations. An additional clause-DAG adapter must
actually construct these data; the current public replay theorem accepts the
polynomial DAG directly.

**Rank boundary.** Here `spanRank` is the rank of the affine polynomials with
their constant coordinates included. The module does not yet identify it with
the codimension of a nonempty affine zero-flat. Inconsistent affine clauses
have empty zero-flats and require separate handling. These geometric facts
must not be silently inferred from the basis-extraction theorem.

## 3. The connected dimension theorem

[`DimensionBudget.lean`](../formal_pc/ProofLab/DimensionBudget.lean) proves the
finite-dimensional linear-algebra step. The ambient vector space and the
individual restriction codomains may be infinite-dimensional. Only `U` needs
to be finite-dimensional; for finitely many variables this follows from the
uniform ordinary degree bound on `U`.

For a finite family of linear maps `L a` from `U`, it maps `U` into the product
of the individual images. Rank-nullity and an injective map from the joint
kernel into `U ∩ W` yield

\[
          \dim U\le\dim(U\cap W)+\sum_a\dim(\operatorname{range}L_a).
\]

[`DAGDimension.lean`](../formal_pc/ProofLab/DAGDimension.lean) composes this
argument with the actual replay theorem. Its restriction hypothesis is
pointwise: membership in the joint kernel forces vanishing on every discarded
node's nonzero locus. It then **proves** the joint-kernel-to-PC implication
internally. With explicit upper bounds `budget a` on the image dimensions,

\[
 \dim U\le\dim\bigl(U\cap C_{k+3R}(F)\bigr)+\sum_a\mathrm{budget}(a).
\]

If `U` is separated from the actual ordinary-PC consequence space, the
intersection term is zero. An empty index type is permitted. A finite index
type can also represent distinct loci rather than repeated node occurrences.
Neither conclusion assumes final PC derivability as an unproved premise.

## 4. What remains before the full exponential bound is formalized

| Remaining bridge | Exact obligation |
|---|---|
| Affine geometry | For a consistent affine clause, identify the relevant span rank with zero-flat codimension; handle an empty zero-flat explicitly. |
| Restriction functions | Construct the actual restriction maps and prove their joint kernel gives the pointwise vanishing needed above. |
| Squarefree image dimension | Prove the restriction image bound `b_k(t) = sum_{j≤min(k,t)} binomial(t,j)` on a `t`-dimensional Boolean flat, including the degree behavior under affine coordinates and squarefree reduction. |
| Source-DAG adapter | Construct the retained raw-input/compressed-derived polynomial DAG from a concrete affine-clause DAG and connect its geometric rank cut. |
| Separated space | Formalize the published graph-reduction interface, actual-PC annihilation, and the empty-support monomials fixed by the reduction. |
| Quantitative existence | Formalize the connected-set count, positive-association estimate, bounded-occurrence formula existence, and final parameter inequalities. |

In particular, **ordinary affine substitution alone does not justify the
squarefree image bound**. A degree-at-most-`k` ordinary polynomial in `t`
variables has an available ambient dimension `binomial(t+k,k)`. To use `b_k(t)`
one must work with Boolean functions or prove and account for squarefree
reduction. The current dimension theorem deliberately takes image bounds as
explicit hypotheses. They are not hidden axioms about affine restrictions.

The next cycle should close the affine geometry and actual restriction-image
steps, then attack the graph-reduction interface. Increasing finite instance
sizes cannot discharge these obligations. The paper proof is preserved with
its evidence level; this cycle does not enlarge its asymptotic claim.

## 5. Provenance, verification, and reproducibility

The three imported foundation files are unmodified MIT-licensed code by
Kamil Braun from Noemesis, pinned at
[`kbr-/math-research@25239211058ef718402a908b3272f01480c159c4`](https://github.com/kbr-/math-research/tree/25239211058ef718402a908b3272f01480c159c4).
They contain 18,251 bytes in total. Both Git blob SHA-1 and SHA-256 are checked.
The original licensing notice and MIT text are retained. This is selective
reuse of the ordinary-PC, completed-line reuse, and Boolean-reduction
foundations, not verification of that repository's main bit-PHP theorem.

The initial hosted build compiled all three pinned foundations and found a
small set of elaboration failures in the lab modules. These included a Lean
comment delimiter in an attribution string, explicit binary-field cases,
universe/decidability inference, and a dimension rewrite. The theorem statements
were not weakened to evade these errors. Typed explicit equalities resolved a
later literal-injectivity elaboration timeout without increasing the heartbeat
limit. A focused independent statement audit also required the finite variable
type to be stated explicitly in this document. The corrected package passed
both the build and all 38 axiom audits. Failed compilation is not counted as
verification.

The package pins Lean `4.34.0-rc2` and Mathlib
`67248ba34806c60bf24b5e99f0f09946ffc465c9`; the original core package remains
on Lean `4.19.0`. The dedicated
[CI workflow](../.github/workflows/ordinary-pc.yml) builds `ProofLab` and queries
the actual transitive axiom sets for the explicit theorem list. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. Cached Mathlib
dependencies use the standard Mathlib cache; this is not an independent
kernel replay of every cached dependency.

The Python reproduction driver separately checks source integrity and hashes
the new sources/configuration. It does not run Lean or transform source hashes
into a formal proof claim. The 62 deterministic reports and 388 existing tests
continue to audit finite computations; none proves an asymptotic lower bound.
The observed formal-audit JSON is a provenance record and is not counted as a
new deterministic finite-experiment report.
