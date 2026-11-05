# Parity queries: existing lower bounds and the exact interface to this lab

Research checkpoint: 2026-11-05. The results identified as
published below are **prior work**, not discoveries of this repository.
The final section separates them from the phase-19 synthesis and the
remaining mathematical obligation. None is an unrestricted SAT time lower
bound or a resolution of P versus NP.

## 1. Specify the terminal rule before applying a lower bound

A parity query asks for a bit

\[
                 \ell(x)=\sum_{i\in Q}x_i\pmod 2.
\]

The two outgoing edges specify the two possible answers. A **raw-clause
leaf** names an original clause falsified by every Boolean assignment
consistent with that path. The path is an affine system over F2; the leaf
condition is checked by Gaussian elimination. Wide queries are represented
explicitly, including all their variable indices.

These are the clause-search parity decision trees corresponding to
**tree-like resolution over parities**, usually written `Res(⊕)` or
`Res(lin_F2)`. Itsykson–Sokolov introduced this setting, first in 2014 and
in the expanded [2020 journal paper][IS]. The paper also shows why explicit
linear systems, including ordinary Tseitin parity formulas, can be easy for
this model despite being hard for variable-query DPLL. Thus a large lower
bound for ordinary resolution does not by itself survive parity queries.

The [phase-18 terminal rule](conditional_localization.md) is different.
After the path assumptions, it permits a resolution DAG of bounded clause
width, then locally valid integer affine equalities/congruences, then a
weighted contradiction. A leaf need not identify one raw clause falsified
throughout its path. Moduli may differ between leaves. Extending the
queries while retaining this terminal rule does **not** produce the same
model as a raw-clause parity tree.

### A direct encoding and bit-cost check

Here is the raw-leaf correspondence in the resource convention needed by
this repository. If the path is

\[
 A=\bigwedge_i(\ell_i=b_i),\qquad
 D_A=\bigvee_i(\ell_i=1-b_i),
\]

then a valid leaf naming an input clause C has `C ⇒ D_A`. This is a
semantic weakening in modern `Res(⊕)`, and its implication is
Gaussian-checkable. At an internal query on a linear form h, the two
children derive

\[
             D_A\lor(h=1),\qquad D_A\lor(h=0).
\]

Resolving them derives `D_A`. At the root, `D_A` is the empty clause.
For L leaves this uses at most `3L−1` proof lines, counting separately a
copy of the input axiom and its weakening at each leaf. There is no sharing
between different branches.

One can first remove any query implied by previous path equations, keeping
its uniquely compatible child. Every surviving path then contains at most
n independent equations. Each displayed linear clause has at most n
linear forms, each using n coefficient bits and a constant bit. Thus the
conversion has `O(n² L)` dense equation bits, apart from the input-clause
copies and ordinary index encoding. It can be constructed with polynomial
work in n plus the explicit tree size. This proves that exponentially large
proof-size requirements cannot be avoided by hiding a wide query inside a
unit-cost label.

When a source uses syntactic rather than semantic weakening, over F2
Gaussian row operations compile the latter to a polynomial-length unary
chain of addition, weakening and simplification. Such a chain preserves
tree shape. A documented construction is
[Gryaznov–Ovcharov–Riazanov, Lemma 4.4][GOR]. For asymptotic transfer we keep
the polynomial overhead rather than assert equality of different authors'
bit-size conventions.

## 2. A direct exponential bound already applies to the phase-16 family

[Part–Tzameret][PT], Section 9, Theorems 43–44, combine a tree-size versus
principal-width inequality with simulation by ordinary polynomial calculus.
For a fixed finite field, principal width and ordinary linear-clause width
are within a constant factor. In the full paper's theorem statement the
PC degree is `O(width)`; its introductory shorthand should not be used to
claim an exact constant.

Consequently, for an ordinary k-CNF F, a raw-clause parity tree with L
leaves yields

\[
 D_{\mathrm{PC}_{\mathbb F_2}}(F)
       =O\!\left(\log(L+1)+\log(n+1)+k\right).             \tag{1}
\]

The harmless logarithmic n term allows the polynomial syntactic/bit
encoding overhead above. Corollary 46 of the same paper explicitly gives,
for random k-CNFs at density Δ and a fixed finite field, the lower bound

\[
 2^{\Omega(n/(\Delta^{2/(k-2)}\log\Delta))}
\]

with high probability, in the stated regime `k≥3`,
`Δ=o(n^{(k−2)/2})`. Fixed density above a satisfiability threshold gives an
exponential bound. Field-dependent constants are not uniform in growing
field size.

**Application, not a new general theorem.** The
[phase-16 construction](correlation_proof_boundary.md#4-a-scalable-control-in-the-same-proper-linear-3-cnf-class)
has ordinary PC degree `Ω(n)` over F2, with raw clause width three. Applying
(1) gives `L=2^{Ω(n)}` for **arbitrary-support raw-clause parity trees** on
that family. No new gadget is required for this conclusion. The
[direct phase-19 deduction proof](parity_pc_bridge.md) additionally supplies
an exact degree accounting and permits degree-bounded PC proofs at leaves.
The raw-leaf result is strictly
more general in query support than a bound for short parities, but uses a
more restrictive terminal certificate than the integer-affine leaves.
It is not legitimate to substitute those leaves into (1) without proving
an additional simulation. Section 6 of the direct phase-19 note proves
one such simulation for conditional integer leaves with a common
characteristic-two detector, at degree `max(2,w+1,b,D)`. Its hypotheses
and detecting-digit charge do not cover arbitrary mixed-characteristic
terminal rules.

In particular, the [phase-18 switched two-field family](field_split_boundary.md)
is a concrete warning about such a substitution: its ordinary PC degree is
linear over every field, yet one selector query followed by different
modular terminal certificates suffices. Its two leaves cannot simply be
replaced by constant-cost raw-clause leaves. The phase-16 and switched
families have different incidence structures.

## 3. A reusable lifting theorem for arbitrary parity trees

[Chattopadhyay–Mande–Sanyal–Sherif, ITCS 2023, Theorem 2][CMSS], prove the
following statement for **every relation** `f⊆{0,1}ⁿ×R`:

\[
        \operatorname{PDTsize}(f\circ g)
               \ge 2^{\,k\operatorname{DT}(f)}.             \tag{2}
\]

Here `DT` is minimum worst-case ordinary decision-tree depth and `PDTsize`
counts nodes. The gadget `g:{0,1}ᵐ→{0,1}` must be k-stifled: for every set
of at most k input coordinates and either desired output, some fixing of
the other coordinates forces that output. Majority on three bits and the
three-bit indexing function are 1-stifled. The result applies to partial
functions and search relations, not just total Boolean functions.

For a CNF, substitute independent copies of g for its variables and encode
each substituted input clause by an equivalent CNF. Any falsified lifted
raw clause identifies a falsified base clause. Hence the harder lifted
raw-clause search inherits (2). At constant base width and constant gadget
size this increases variables and clauses by only a constant factor.
This is useful beyond one graph family, but does not make stronger integer
terminal leaves automatically valid outputs of that search relation.

## 4. What is known when branches share derived information?

A **parity decision DAG** has an affine system at each node. For a query
`h=b`, the parent's system together with that answer must imply the
child's system. Every sink's system must falsify a raw clause. This
implication condition must hold on **each incoming edge**; merely merging
isomorphic-looking subtrees under different assumptions is insufficient.

The strongest general-purpose width lifting result located in this check
is [Itsykson–Podolskii–Shekhovtsov, CCC 2026][IPS]. Corollary 1.3 states
that if every ordinary resolution refutation of F has width at least w,
then, for any fixed-size 1-stifling g, a `Res(⊕)` refutation of `F∘g` with
S lines has depth

\[
                         \Omega(w^2/\log S).                \tag{3}
\]

Theorem 1.6 gives the unconditional size bound `S≥w(w+1)/2`. These results
permit DAG reuse. With `w=Ω(n)`, (3) gives `exp(Ω(n^ε))` size for depth
`O(n^{2−ε})`. **Removing the depth restriction does not give a
superpolynomial bound**: the size statement is quadratic. The July 2026 paper identifies unrestricted superpolynomial `Res(⊕)` size
lower bounds as open at that time. A newer preprint described below claims
to resolve that benchmark; the earlier status must not be presented as an
up-to-date impossibility of such a result. The IPS depth counts resolution
steps; its size counts linear clauses, not coefficient-bit operations.

Applying this published theorem to the majority lift of a base family with
linear resolution width is a useful DAG stress test. It is a different
family from the unlifted phase-16 CNF, and an existing theorem application,
not an original unrestricted lower bound.

### September 2026 preprint: an unrestricted claim to audit

[Kamil Braun, arXiv:2609.23015v2][Braun], first submitted September 19 and
revised November 3, claims an unrestricted DAG `Res(⊕)` lower bound for bit
pigeonhole formulas. With n=2^ℓ holes and n+1 pigeons, Theorem 1.1 asserts
more than `exp(n/(32768 ℓ²))` proof lines for `ℓ≥32`, without depth or
regularity restrictions. The author supplies Lean source links pinned to
commit `8904bf09`; Appendix C maps the claims to formal declarations.
This note records the claim and provenance, **not a completed independent
verification of its proof or formal statement**.

The preprint's Theorem 9.1 is a potentially reusable criterion involving a
large space of low-degree polynomials disjoint from all low-degree PC
consequences. Its premise is stronger than an ordinary PC refutation-degree
lower bound. The output of its proposed elimination is a nonzero polynomial,
not necessarily one. Neither its claimed lower bound nor its formal sources
can be imported merely by substituting the phase-16 PC degree into that
criterion. Semantic correspondence, hypotheses and build evidence require a
separate audit before use.

### A nearly exhaustive lower bound has a different width regime

[Efremenko–Itsykson, STOC 2026][EI], Theorem 1.1 / Corollary 8.4 of the
full paper, gives polynomial-size formulas on N variables for which a
fragment containing depth-N `Res(⊕)` requires
`2^{(1−(7/2)ε)N}` lines, for each fixed positive ε. The input clause width
is `O_ε(log N)`. The theorem also covers tree-like and regular `Res(⊕)`
through the stated simulations. Its construction uses different random
gadgets at different base variables. This is a particularly strong
**restricted proof-system** bound, not a proof of unrestricted SETH,
and not a constant-width-3 result. The width and depth qualifications must
accompany any reuse of the title or exponent.

## 5. Other general criteria, and the next obligation

[Gryaznov–Ovcharov–Riazanov][GOR], Theorems 3.1–3.2, give an extensibility
criterion: relative to a satisfiable set H of protected clauses, every
small linear system that has an H-model must have an H-model satisfying
each remaining input clause separately. If the threshold is m equations,
this yields tree-like size at least `2^m` and clause-space at least m.
The protected set and universal extension condition must be established;
ordinary hypergraph expansion alone is not a verification of them.

The inventory for this research cycle is therefore:

| Statement | Evidence and attribution | Scope that must remain explicit |
|---|---|---|
| Arbitrary-support parity trees are exponentially large on the phase-16 family | Published PC simulation and tree-size/width results applied to the existing PC-degree bound | Raw-clause leaves; no DAG reuse |
| Constant-size gadget lifting gives a general source of parity-tree lower bounds | Published CMSS theorem (2) | Lifted search relation and raw-clause output |
| Linear ordinary width yields quadratic DAG size and a near-quadratic depth tradeoff after lifting | Published IPS theorem (3) | This theorem does not give unrestricted superpolynomial DAG size |
| Unrestricted DAG exponential size for bit PHP | Braun September/November 2026 preprint and supplied Lean sources | Claim recorded; independent audit needed before adoption |
| Bounded-support parity queries retain an exponential lower bound with the integer-affine terminal rule | [Phase-19 absorption synthesis](parity_localization.md), with a full proof | Query support, width and local scope are charged; arbitrary moduli are allowed |
| Arbitrary-support parity queries with same-field degree-bounded PC leaves | [Phase-19 deduction synthesis](parity_pc_bridge.md): `Σ 2^{d_leaf} ≥ 2^{D_PC}` | One common field F2; no cross-characteristic gluing |
| Arbitrary-support parity queries with conditional integer leaves detected in characteristic two | [Conditional simulation](parity_pc_bridge.md#6-conditional-integer-leaves-with-a-common-characteristic-two-detector), at leaf degree `max(2,w+1,b,D)` | Proper CNF; verified local/path row validity; genuine detecting digit `D=2^{v₂(R)}` charged at every leaf |
| Arbitrary-support parity trees with the full mixed-integer terminal rule | Not established by the papers above or by this note | Needs a new extension argument, a sound simulation, or a counterexample |

These results should be retained as reusable lower-bound tools. They do
not warrant repeatedly running larger instances of an already understood
barrier. The useful remaining question is whether a precisely defined new
rule escapes the supported lower-bound model while maintaining polynomial
certificate verification **and discovery** costs.

## Primary references

- [IS] Dmitry Itsykson and Dmitry Sokolov, *Resolution over linear equations
  modulo two*, Annals of Pure and Applied Logic 171(1), 102722 (2020);
  earlier conference work in 2014. [Journal and DOI][IS].
- [PT] Fedor Part and Iddo Tzameret, *Resolution with Counting: Dag-Like
  Lower Bounds and Different Moduli*, ITCS 2020; author full version dated
  November 13, 2020. Section 9, Theorems 43–44 and Corollary 46,
  printed pages 37–39. [Full paper][PT].
- [CMSS] Arkadev Chattopadhyay, Nikhil S. Mande, Swagato Sanyal and Suhail
  Sherif, *Lifting to Parity Decision Trees via Stifling*, ITCS 2023.
  Theorem 2, page 33:3; proof-complexity application, Section 1.1.
  [Published paper][CMSS].
- [GOR] Svyatoslav Gryaznov, Sergei Ovcharov and Artur Riazanov,
  *Resolution Over Linear Equations: Combinatorial Games for Tree-like
  Size and Space*, ACM Transactions on Computation Theory (2024),
  DOI 10.1145/3675415. [Author manuscript][GOR].
- [Braun] Kamil Braun, *An exponential lower bound for the bit pigeonhole
  principle in resolution over parities*, arXiv:2609.23015v2 (2026).
  [Full preprint][Braun]; [supplied research repository](https://github.com/kbr-/math-research).
- [EI] Klim Efremenko and Dmitry Itsykson, *Strong ETH Holds for Bounded-Depth
  Resolution over Parities*, STOC 2026, pages 898–909,
  DOI 10.1145/3798129.3800804. [Full author paper][EI].
- [IPS] Dmitry Itsykson, Vladimir Podolskii and Alexander Shekhovtsov,
  *Resolution Width Lifts to Near-Quadratic-Depth Res(⊕) Size*, CCC 2026,
  published July 23, 2026. Corollary 1.3, Theorem 1.6 and Sections 2.4–2.5.
  [Published paper][IPS].

[IS]: https://doi.org/10.1016/j.apal.2019.102722
[PT]: https://www.doc.ic.ac.uk/~itzamere/Res-Lin-Two.pdf
[CMSS]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol251-itcs2023/LIPIcs.ITCS.2023.33/LIPIcs.ITCS.2023.33.pdf
[GOR]: https://arxiv.org/html/2404.08370v2
[IPS]: https://drops.dagstuhl.de/storage/00lipics/lipics-vol383-ccc2026/LIPIcs.CCC.2026.13/LIPIcs.CCC.2026.13.pdf

[EI]: https://eccc.weizmann.ac.il/report/2025/188/download/

[Braun]: https://arxiv.org/pdf/2609.23015v2
