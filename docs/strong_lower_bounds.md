# Reusable lower bounds: statements, provenance, and limits

This register preserves generalizable lower bounds even when they do not
resolve P versus NP. A bound for a specified proof system is recorded with
that system, its encoding, and every resource restriction. A finite failed
search is not entered as an asymptotic theorem. Published results, deductions
for this repository's models, and newly encountered unverified claims are
kept distinct. Last updated: **2026-11-05 JST**.

## 1. Common supports defeat every modulus in a local integer suffix

**Provenance:** the lab's phase-18 application of established minimal-support
and pooled-support arguments. The devices are attributed to Ben-Sasson–Wigderson
and Mikša–Nordström in the [full proof](support_localization.md).

Suppose a proper ternary CNF has unique-neighbor expansion
$|\partial U|\ge\delta|U|$ for every nonempty raw clause set of size at most
$s$. After any ordinary resolution/weakening prefix of width at most $w$,
all learned clauses on a scope $S$, $|S|\le b$, have one common original
support of size at most $\lfloor |S|/\delta\rfloor$, provided

\[
2\lfloor w/\delta\rfloor\le s,
\qquad 2\lfloor b/\delta\rfloor\le s.
\]

Matching outside one or two coordinates gives complete coordinate faces
among the local models. Their affine integer lattice, including the
multilinear moment lift through degree two, is full. Thus no final weighted
sum of locally valid affine integer equalities/congruences can refute the
formula. The modulus, detecting digit, number of laws, and coefficient bit
lengths are unrestricted. This is stronger than failure of a bounded search.

For the phase-16 family, $\delta=1/2$ and $s=\lfloor10^{-16}n\rfloor$,
so the specified one-sum refutation requires $\max(w,b)>s/4$.
It does not cover inequalities, extension coordinates, additional Boolean
inference from an arithmetic row, or arbitrary proof systems.

## 2. Short parity questions with arbitrary-modulus integer leaves

**Provenance:** the phase-19 extension and parameter optimization of the lab's
closure/matching proof. No novelty claim is made for the underlying closure
or Prover–Delayer method. See [the complete model and proof](parity_localization.md).

Let raw clauses have width at most $r$, with neighborhood expansion
$|N(U)|>\alpha|U|$ for $1\le|U|\le s$. Choose

\[
\max(1,r/2)<\beta<\alpha,\qquad \delta=2\beta-r,
\qquad R=\max(1,2\lfloor w/\delta\rfloor,2\lfloor b/\delta\rfloor).
\]

If $s\ge R$, any finite tree of parity queries of support at most $q\ge1$,
with the stated width-$w$/scope-$b$ conditional integer refutation at every
leaf, has at least

\[
       2^{\left\lfloor(\alpha-\beta)(s-R)/q\right\rfloor}
\]

leaves. An internal question may adapt to previous answers; every leaf may
choose different moduli and weights. Leaf resolution proofs can be arbitrary
length DAGs. Sharing conclusions between different query branches is excluded.

For the existing ternary family, let $M=\max(1,w,b)<s/4$. Optimizing the
closure threshold yields

\[
       L\ \ge\ 2^{\left\lfloor(\sqrt{s}/2-\sqrt M)^2/q\right\rfloor}.
\]

At fixed $w,b,q$ this is exponential in $n$. With $M=o(n)$, a polynomial
leaf count requires $q=\Omega(n/\log n)$. These are necessary conditions
in this model, not an algorithm when they hold. The expansion constant is
tiny and existential; small experiments do not have this numerical hardness.

The invariant charges newly exposed coordinates. A single rank-one question
on the private leaves of a nine-clause sunflower absorbs all nine clauses,
disproving the proposed replacement of exposure by equation rank. Both
answers remain satisfiable. That counterexample limits this proof strategy;
it is not a proof that unrestricted parity queries are efficient.

## 3. Arbitrary parity questions with bounded-degree proofs over one field

**Provenance:** the phase-19 explicit deduction-and-tree argument, using
standard polynomial-calculus deduction and binary branching-rank ideas.
It is a reusable synthesis; no claim to a new lower-bound method. See
[the proof and precise leaf interface](parity_pc_bridge.md).

Let $D_2(F)$ be the minimum degree of an ordinary polynomial-calculus
refutation over $\mathbb F_2$, including Boolean axioms. Consider any parity
query tree on the original variables, with no bound on query support.
At leaf $\lambda$, assume an actual conditional PC proof from $F$ and the
path's affine equations of degree at most $d_\lambda\ge2$. Then

\[
       \boxed{\quad \sum_{\lambda}2^{d_\lambda}\ \ge\ 2^{D_2(F)}.\quad}
\]

In particular, if all $d_\lambda\le d$, then
$L\ge2^{D_2(F)-d}$ when $D_2(F)\ge d$.
The proof discharges one affine assumption by multiplying its conditional
proof by the complementary affine form. This raises ordinary degree by at
most one; the other branch can use the resulting complementary equation.
Choosing the smaller branching rank first gives a root degree no greater
than $d+\lfloor\log_2 L\rfloor$ in the uniform case.

All leaves must use **the same field**. A certificate valid modulo three,
or an arbitrary integer certificate, is not automatically a small-degree
$\mathbb F_2$ proof. Nor does this degree simulation assert polynomial
expanded proof length: products of wide linear forms can have many monomials.
This theorem does not handle arbitrary sharing between branches.

The [conditional integer simulation](parity_pc_bridge.md#6-conditional-integer-leaves-with-a-common-characteristic-two-detector)
gives a concrete sufficient interface. At a leaf, allow width-$w$ resolution
from the CNF and path-implied clauses, local integer rows on at most $b$
coordinates checked against the projected affine path context, and even
arbitrary-support integer rows valid on the path alone. For a weighted final
modular sum with modulus $m$, residual $R$, and the usual coefficient/modulus
compatibility, require an actual characteristic-two detector:
$v_2(R)<v_2(m)$. Set $\Delta=2^{v_2(R)}$. The conditional PC degree is at most

\[
                         \max(2,w+1,b,\Delta).
\]

Exact final sums with nonzero $R$ are also covered, with exact compatibility
and the same charged digit. Different leaves may have different final
moduli, but all must pass this common-characteristic condition. For example,
$m=6,R=2$ fails it even though $m$ is even. On the phase-16 family, sublinear
$w,b,\Delta$ force exponentially many leaves regardless of query support.
This corollary is a paper proof; the executable PC converter checks the
generic tree bridge and raw-clause leaves, not every arithmetic interface
described by the theorem.

## 4. Published arbitrary-parity and DAG results used for comparison

These are **prior results**, not discoveries of this repository.

| Result | Precise usable conclusion | Boundary |
|---|---|---|
| Part–Tzameret, Computational Complexity 2021, Theorems 43–44 | A fixed-field PC degree lower bound implies an exponential tree-like resolution-over-linear-equations bound, via size/width and width/degree simulations. In particular, the phase-16 family is exponentially hard for arbitrary parity trees ending in a falsified raw clause | This raw-leaf conclusion does not by itself handle mixed-field integer terminal proofs |
| Chattopadhyay–Mande–Sanyal–Sherif, ITCS 2023, Theorem 2 | For every relation $f$ and every $k$-stifled gadget $g$, parity decision-tree **node size** is at least $2^{k\,\mathrm{DT}(f)}$ for $f\circ g$ | Applies to the composed relation and its specified outputs; does not automatically lift a stronger arithmetic terminal oracle |
| Itsykson–Podolskii–Shekhovtsov, CCC 2026, Corollary 1.3 and Theorem 1.6 | A resolution width lower bound $w$ for $F$ gives depth $\Omega(w^2/\log S)$ for size-$S$ Res($\oplus$) proofs of $F\circ\mathrm{MAJ}_3$, and unrestricted size at least $w(w+1)/2$ | The depth/size tradeoff is not an unrestricted exponential DAG-size bound |
| Efremenko–Itsykson, STOC 2026 / ECCC TR25-188, Theorem 1.1 | For every fixed $\varepsilon>0$, there are polynomial-size CNFs on $N$ variables with a $2^{(1-7\varepsilon/2)N}$ size bound for a fragment including depth-$N$ Res($\oplus$) | Width grows as $O_\varepsilon(\log N)$; this does not establish SETH for general algorithms or a fixed 3-CNF claim |

Primary links, exact translations, bit costs, and theorem locations are in
[the literature note](parity_query_prior_work.md). Do not turn a statement
about the literature at one publication date into a timeless open-status claim.

## 5. A newer unrestricted-DAG claim: recorded, not yet adopted as a lemma

Kamil Braun's [arXiv:2609.23015v2](https://arxiv.org/abs/2609.23015v2),
first submitted 2026-09-19 and revised 2026-11-03, claims that every
unrestricted DAG-like Res($\oplus$) refutation of bit PHP with $n+1$ pigeons
and $n=2^\ell$ holes has more than

\[
           \exp\!\left(\frac{n}{32768\ell^2}\right),
           \qquad \ell\ge32,
\]

proof lines. The manuscript supplies Lean links and a more general criterion
based on a separated polynomial space. The variable count is
$(n+1)\ell$, and the CNF has polynomial length in $n$; do not substitute
the number of holes for the original input length without accounting for it.

The [bounded source audit](braun_resoplus_audit.md) records exactly what was
inspected. This cycle does not independently rebuild and certify the full
dependency closure or complete a specialist review of the mathematics.
Consequently the claim is not a premise of sections 1–3. It should neither
be ignored by calling the unrestricted problem simply open, nor be treated
as established solely because the abstract reports a formal proof.

## 6. What would make a lower bound relevant to the final goal?

Every result above restricts a proof language, a branching structure, or a
degree/width/scope resource. It can rule out an algorithm whose outputs are
provably simulated by that model with controlled cost. It does not bound
every deterministic algorithm for SAT. A complete P versus NP argument must
meet the [solution criteria](solution_criteria.md), including the relevant
all-algorithm or all-input quantifiers. None of these entries meets that final
criterion, and none is recorded as a P versus NP solution candidate.
