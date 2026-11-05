# Bounded source audit of the 2026 unrestricted Res(⊕) claim

**Status on 2026-11-05: source-interface inspection only.** This note records a
recent claim that materially changes how the literature should be described.
It does not report an independent kernel build, a complete mathematical audit,
acceptance of the theorem, or a counterexample to it. None of this repository's
phase-19 lower bounds depends on accepting the claim.

Kamil Braun's [arXiv:2609.23015v2](https://arxiv.org/abs/2609.23015v2), revised
2026-11-03, claims that unrestricted DAG-like resolution over parities requires
more than $\exp(n/(32768\ell^2))$ clauses to refute bit-PHP with $n=2^\ell$ holes,
$n+1$ pigeons, and $\ell\ge32$. The abstract and revision note state that the
main results and dependencies are formalized in Lean and that revision 2
changes the exposition, not the theorem statements or Lean proofs. It would
therefore be inaccurate to present the earlier literature's unrestricted-DAG
open-problem statement as the only current information.

## 1. Revision and inspection boundary

**Phase-20 follow-up:** [the bounded dependency audit](braun_generic_audit.md)
adds 17 pinned source files. The lab then obtained a
[direct common-annihilator criterion](affine_dag_annihilator.md), with a
separate proof that does not import the preprint's registry/removal theorem.
The historical twelve-file inventory below remains the scope of phase 19;
neither phase claims a complete upstream kernel build.

The upstream repository is [`kbr-/math-research`](https://github.com/kbr-/math-research).
Its main ref was pinned to
[`25239211058ef718402a908b3272f01480c159c4`](https://github.com/kbr-/math-research/tree/25239211058ef718402a908b3272f01480c159c4)
before reading any source. The twelve Lean files in section 5 were fetched at
that exact revision. Their content lengths and Git blob SHA-1 values were
recomputed locally and matched the tree entries: 76,217 bytes in total.

Additional orientation reads were the root README, the formalization README,
the bit-PHP formalization route, the pinned `lakefile.lean` and `lean-toolchain`,
and the Lean workflow definition. The toolchain is `leanprover/lean4:v4.34.0-rc2`
and the Mathlib pin is `67248ba34806c60bf24b5e99f0f09946ffc465c9`.

No upstream program, workflow, installer, or Lean build was run. The checked
source files were stored only as temporary audit inputs, not copied into this
repository's formal library. Their import closure, Mathlib, compiled artifacts,
and complete transitive axiom sets were **not** checked here. In the inspected
files no unfinished Lean proof or custom axiom declaration was found; this
bounded text inspection is not a substitute for `#print axioms` and kernel
replay on the complete imported proof.

## 2. Does the visible statement concern the advertised proof system?

The main statement is `MathResearch.bitPHP_exponential` in
[`BitPHPExponential.lean`](https://github.com/kbr-/math-research/blob/25239211058ef718402a908b3272f01480c159c4/formalization/claims/BitPHPExponential.lean).
Its explicit mathematical arguments are:

- a bit length $\ell\ge32$;
- a natural number $S$ and a list of $S$ finite affine clauses over the original
  coordinate type `Fin (2^ℓ+1) × Fin ℓ`;
- an `AffineDAG` derivation of that list from `usualBitPHPInitials`;
- a node of the list whose clause is empty.

Its conclusion is the strict bound
$\exp(2^\ell/(32768\ell^2))<S$. There is no additional hypothesis in this
top-level theorem requiring the alleged lower bound, a PC degree bound, a
special expansion property, regularity, tree-likeness, or a depth limit.
The neighboring superpolynomial theorem has the corresponding eventual
quantifiers for every fixed real exponent $K>0$.

The inspected definitions support the advertised interpretation:

| Formal object | What the source actually defines |
|---|---|
| `ParityClause` and `clauseHolds` | A finite set of affine maps over `ZMod 2`; a clause holds when at least one map has value one. This is a disjunction of affine binary equations, with constants absorbed into the maps. |
| `AffineDAGStep` | An initial clause, semantic weakening from an earlier node, complementary-parity resolution from two earlier nodes, or an arbitrary sound binary semantic consequence of two earlier clauses. |
| `AffineDAG` | One such step for every topologically indexed node. Earlier parents may be reused arbitrarily; there is no restriction on reuse, depth, queried support, or repeated pivots. |
| `usualBitPHPInitials` | For every pair of distinct pigeons and every $\ell$-bit hole label, a clause saying that at least one of those two pigeon labels differs from that hole label. Thus both pigeons cannot occupy that same hole. |
| `compactPairClause` | A disjunction of the pair's bitwise inequalities. It implies each usual CNF collision clause; `compact_clause_entails_CNF` proves this direction. |

In particular, the visible `AffineDAG` interface is not a tree proof in
disguise. Its binary semantic rule permits a stronger local consequence rule
than just the displayed syntactic resolution rule. A lower bound for this
interface, if its proof and all definitions are validated, covers the ordinary
unrestricted resolution/weakening convention. The input contains all $2^\ell$
hole labels, so there is no promise that only a special subset of hole
assignments is considered.

This addresses a frequent potential failure mode in formal lower-bound
claims: proving a theorem about a narrower object than the advertised one.
**No such mismatch was found in these inspected interfaces.** It does not
establish the correctness of all uninspected dependencies.

## 3. What is visible in the algebraic transfer and final assembly?

`PolynomialCalculus.Derives` is an inductive ordinary PC derivation over actual
multivariate polynomials. Its rules are zero, an input polynomial of bounded
ordinary degree, addition, scalar multiplication, and multiplication by one
variable when the result stays within the degree bound. Its definition does
not identify bounded-degree PC with Nullstellensatz or assume completeness of
some stronger rule.

`usual_bitPHP_PC_transfer` takes the actual source DAG and constructs a fixed
registry with at most $3S+\binom{n+1}{2}$ clause slots. In an extended polynomial
system it produces a refutation through degree
$\max(2h+\ell,4h+1)$. The registry contains fresh coefficient variables,
Boolean axioms, and companion equations. Its clause values are **not** simply
added as unproved axioms: the inspected code gives initial-value proofs and
replays source nodes in topological order. In the final application $h=3\ell$,
so the displayed degree is $12\ell+1$.

The other imported endpoint, `affine_family_exclusion_of_square`, takes
explicit numerical inequalities for $m,\ell,M,k,D$ and the number of proper
high-rank blocks. Its conclusion excludes a degree-$D$ refutation of that
extended system. Its visible proof invokes a common affine kernel, simultaneous
family removal, and a row-cube separator. The final exponential theorem supplies
the numerical inequalities and block count itself. It does not leave this
exclusion as an extra assumption of the final theorem.

This is a check of the theorem's assembly and interfaces. The substantive
kernel-construction, family-removal, matching-moment, decoder, and topological
dependencies were not all read or independently proved in this bounded audit.
The visible assembly is therefore evidence that there is a concrete proof to
inspect, not evidence that its entire dependency chain has already passed an
independent verification here.

The upstream import-only aggregate is `claims.BitPHPPreprintRevision1`. Its
workflow calls the upstream verifier and then
`lake env leanchecker --fresh claims.BitPHPPreprintRevision1`. A workflow
definition is not a successful run. This audit does not claim a fresh local
or hosted verification of that aggregate, or a complete source-to-artifact
correspondence for any previously produced build.

## 4. A generalizable sufficient condition worth retaining

The inspected `generic_CNF_subspace_criterion` records a stronger obligation
than an ordinary PC refutation-degree lower bound. In simplified notation,
let $v$ be the number of original variables, $A$ a finite family of width-$w$
affine clauses covering the source axioms, and `old` an ordinary polynomial
base containing their falsity polynomials and the Boolean axioms. Let
$h,k\ge1$ and

\[
                         D=\max(2h+w,4h+1).
\]

Suppose $U$ is a linear subspace of degree-at-most-$k$ polynomials such that

\[
                 U\cap C_{k(D+1)}(\mathrm{old})=\{0\},
\]

where $C_B$ is the actual bounded-degree PC consequence space. The formal
criterion concludes, for any source refutation with $S$ nodes,

\[
 \dim U\le (3S+|A|)
       \binom{\max(0,v-(h(k+1)+1))+k}{k}.
\]

The maximum with zero spells out the natural-number subtraction in Lean.
The criterion is a conditional general method, and the inspected file's own
scope statement does not claim to construct the required separated subspace
for arbitrary CNFs. Knowing only that $1$ is not derivable at low degree does
not establish that an entire large $U$ has the stated zero intersection.
For the lab, the productive next mathematical question is whether a concrete
family has such a quantitatively large separated subspace, after auditing
the criterion's remaining dependencies. Simply relabeling an existing PC
degree lower bound would omit its main new hypothesis.

Even a complete validation of the bit-PHP claim would establish a lower bound
for the specified Res(⊕) proof system. It would not by itself separate P from NP,
nor automatically cover the lab's mixed-characteristic integer terminal rules.

## 5. Exact source inventory

All paths below are under `formalization/claims/` at the pinned upstream
revision. The hashes are Git blob SHA-1 values, not SHA-256 content hashes.

| Inspected source | Verified Git blob SHA-1 |
|---|---|
| `BitPHPExponential.lean` | `c222191a0a0dd895530ea67148be343be886d4fd` |
| `BitPHPSuperpolynomial.lean` | `81e0c303a23d59c35c740b024d104de1a522cec9` |
| `AffineDAGRegistry.lean` | `af0f0a530304c99be3779e6485dad3fa6aa35fa4` |
| `AffineClauseRegistry.lean` | `119c485d0570368ec9dc2de06805bb1b0fac4834` |
| `AffineForm.lean` | `5e0ab121d0411f1aa056a67f7f087280d3eabfe3` |
| `PolynomialCalculus.lean` | `432f7be7295e3b78183a60148574b16b22e0311e` |
| `BitPHPInitialBridge.lean` | `147d01f5463cc44f59513e0dae0c0181202dc4de` |
| `BitPHPClauseTransfer.lean` | `b67ff0acbc579b85c9239dbea1c3d9516ad75144` |
| `AffineFamilyExclusion.lean` | `ca3ba1e9cbb4cdcd94beffc01a33fcd9fd085e8c` |
| `BinaryAffineZeroCover.lean` | `7fa7435c7ae47822a26288b5d310437faa4cc414` |
| `BitPHPPreprintRevision1.lean` | `4e687cfca44d0c6989f9950732654081b4e2cf4a` |
| `GenericCNFSubspaceCriterion.lean` | `e13ff86d127cbd6b2fffc156c605fc126ddabc89` |

The audit is deliberately bounded to these interfaces and assembly points.
It should be extended by a targeted full import build and transitive axiom/
kernel check before this repository labels the upstream result independently
machine-verified. A further mathematical review would still be needed for the
translation between formal objects and the intended standard proof system.
