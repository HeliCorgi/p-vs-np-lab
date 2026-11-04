# Prior work: current ETH claims, mixed reasoning, and exact signatures

Research snapshot: **2026-11-03 UTC**. The external repository examined for this
phase is `openai/math` at commit
`4eaee87548250b2682affda7d05d947c05554bae`. Links to moving external pages are
dated observations, not immutable verification records.

The most consequential finding is a recent release claiming a subexponential
exact counting algorithm for fixed-width CNF. Its manuscript, Lean statement,
independent compilation reports, and community review have different scopes.
They must be recorded separately. The
[Clay Mathematics Institute page](https://www.claymath.org/millennium/p-vs-np/)
still lists **P versus NP as unsolved** at this snapshot. None of the work
described below supplies a polynomial-time SAT algorithm or a lower bound
against every polynomial-time algorithm.

## 1. The target remains a uniform, all-input theorem

[Cook's official problem description](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf),
Sections 1–2, defines polynomial time using the full encoded input length and
states the NP-completeness consequence. For a constructive `P = NP` result,
it is sufficient to provide one deterministic algorithm deciding every
3SAT instance, prove its correctness, and prove a bound `C (N+1)^c` for fixed
constants `C,c` and encoded length `N`. The algorithm and constants cannot
depend on the particular input. A `P != NP` proof instead has to exclude
every such algorithm for some language in NP.

Our [solution criteria](solution_criteria.md) and
[reverse-engineering note](reverse_engineering.md) track these obligations.
Correctness of an inference, successful experiments, or a short proof for one
family answers only part of them. A proof checker validates the propositions
actually formalized; correspondence with the intended input encoding,
computation model, and complexity statement must also be inspected.

## 2. The October 2026 ETH releases: separate the claims

### 2.1 OpenAI's manuscript and formalized endpoint

The primary artifact is
[The Exponential Time Hypothesis is False, October 25 version](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026).
The pinned
[Lean scope note, family 378](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/378.md)
explicitly distinguishes the following bounds. Here `k` is fixed, `n` counts
variables, `m` counts clauses, and `L` is the canonical encoding's bit length.

| Artifact | Stated scope |
|---|---|
| Lean exact-counting endpoint | A deterministic machine, time `(L+1)^{O_k(1)} 2^{O_k(n (log log n)^2 / sqrt(log n))}`, and polynomially many visited tape cells at every step. |
| October 25 manuscript, arbitrary fixed-width CNF | The sharper bound `(n+m)^{O_k(1)} 2^{O_k(n log log n / sqrt(log n))}`. |
| Manuscript with fixed density `m <= D n` | `(n+m)^{O_{k,D}(1)} 2^{O_{k,D}(n / sqrt(log n))}`. |

Thus a successful check of the advertised Lean endpoint would not by itself
check the manuscript's sharper logarithmic factors. Nor would merely finding
the endpoint name establish that its imported definitions have the intended
meaning.

The [October 26 OpenAI announcement](https://openai.com/index/building-scientific-understanding-with-academic-communities/)
asserts the result and its Lean formalization, calls the released manuscripts
raw research data, and describes further verification and explanation led by
Russell Impagliazzo, Ramamohan Paturi, and Ryan Williams. This is the releasing
organization's report; it is not a substitute for the independent review.

### 2.2 What independent sources currently establish

| Primary source and date | Evidence and limit |
|---|---|
| [Paturi's community examination announcement, October 26](https://ethdiscussion.blog/2026/10/26/eth-refutation-examination-and-discussion/) | Explicitly says the organizers' involvement is not certification; invites independent reconstruction and criticism. |
| [Zane's Lean replication thread, October 30](https://ethdiscussion.blog/2026/10/30/lean-replications/) | Reports local compilations. An October 31 contribution describes comparator acceptance and standard axiom dependencies, while explicitly distinguishing this from checking the informal meaning of the statement. These are the contributors' reports, not builds performed by this literature review. |
| [Ryan O'Donnell's exposition, October 30](https://www.cs.cmu.edu/~odonnell/some_eth_false_exposition.pdf) | Recasts the argument using sparse permanents and interpolation. Its main sparse case is deterministic; Appendix B uses a randomized reduction for arbitrary 3CNF. Its statements should not be substituted for the original deterministic endpoint. |
| [Anthropic's separate ETH artifact](https://github.com/anthropics/formal-math/blob/main/eth/README.md), inspected November 3 | Announces a deterministic `#3SAT` bound `2^{O(n log log n / sqrt(log n))}` and supplies Lean statements and comparator instructions, including a second kernel. Its README explicitly leaves paper-to-statement correspondence to human inspection. This is a separate formalization, not our independent validation of either complete development. |

The [community blog](https://ethdiscussion.blog/) still described the result
as a claimed refutation in its November 1 update. This review did not locate
a declaration there that the complete independent mathematical examination
had finished. That observation is limited to the primary material inspected.

The November 2 preprint
[ETH is Dead, Long Live SH](https://arxiv.org/abs/2611.02650), by the MIT
Hardness Group and coauthors, studies the equivalence of the Stearns–Hunt
hypothesis with a weaker ETH excluding `2^{n^{1-epsilon}}` algorithms, and
consequences for size-controlled reductions. It is relevant new work about
remaining hypotheses. Its use of the ETH release as a starting point does
not itself audit the original proof or establish `P != NP`.

### 2.3 Why the advertised bound would refute ETH but not settle P versus NP

[Impagliazzo and Paturi, *On the Complexity of k-SAT* (2001)](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturi_2001_jcss.pdf)
define `s_k` as the infimum of achievable exponential constants and formulate
ETH using `s_3 > 0`. A correct uniform fixed-`k=3` algorithm with the displayed
subexponential bound would contradict that hypothesis. After duplicate
clauses are removed, fixed-width formulas have only polynomially many
distinct clauses; input processing must still be charged.

The elementary asymptotic comparison is decisive. For either `a=1` or `a=2`,

\[
 f_a(n)=\frac{n(\log\log n)^a}{\sqrt{\log n}}
 \quad\text{satisfies}\quad
 f_a(n)=o(n),\qquad f_a(n)=\omega(\log n).
\]

The corresponding displayed exponential bound is subexponential in `n`,
but is not a polynomial bound. This is a statement about that upper bound,
not a runtime lower bound for the proposed algorithm. A faster analysis or
different algorithm is not excluded. Exact counting also decides SAT by
testing whether the count is positive, but a subexponential counting bound
does not upgrade itself to polynomial time. None of these upper bounds
proves `P != NP` either.

## 3. What the finite measurement identity lets us reuse

The manuscript's subsection
[Separating the sum by fixing measurements](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex)
is a useful, independently inspectable component. Disjoint groups `S_g`
have integer measurements `C_g u`. Once all measurements `y` are fixed,
each assigned factor may depend freely on its own group and on other groups
only through those measurements. Writing the resulting group contribution
as `A_{t,g}`, the identity is

\[
 H(t)=\sum_{y\in\mathcal Y}\prod_g
 \left(\sum_{u\in\{0,1\}^{S_g}:C_gu=y_g}A_{t,g}(u;y)\right).
\]

Each full assignment belongs to exactly one measurement fiber, and
distributivity proves the identity. With at most `2 tau n` measurement rows,
row coefficient `l1` norm at most `D`, and groups of size at most `2n/r`, the
stated enumeration cost is

\[
 \operatorname{poly}(N)(2D+1)^{2\tau n}2^{2n/r}.
\]

The asymptotic algorithm additionally needs its constructed polynomial
replacements and interpolation argument. This finite identity alone does
not supply them or assert universally small signature sets.

### A local specialization and its proof obligations

For this lab, the analogous finite statement can be derived directly for
maps `sigma_g` into finite signature sets, including linear maps over
`GF(2)`. Let

\[
 T_g(s;y)=\sum_{u:\sigma_g(u)=s}A_g(u;y).
\]

If the external dependence of every factor is constant on the corresponding
signature fibers, summing the products of `T_g(y_g;y)` over all signature
tuples gives the exact original sum. The proof is the same partition into
disjoint fibers. This is our finite specialization; it is not an
implementation of the upstream subexponential algorithm.

Three costs remain explicit in any implementation: finding suitable maps,
constructing the local tables, and combining their entries. A sparse matrix
can still have a large image. For example, `sigma(u)=I_b u` uses one nonzero
entry per row but has `2^b` signatures. If each of the `b` coordinates is
individually observable, any signature sufficient to recover all those
observations must be injective: two distinct assignments differ in a
coordinate that the observer can distinguish. Therefore this representation
requires `2^b` states. This argument concerns those specified observations
and an explicit signature table; it does not lower-bound arbitrary SAT
algorithms, symbolic circuits, or all possible factorizations.

Using counts rather than Boolean existence also requires disjoint fibers
and exact arithmetic. A transformation that preserves only satisfiability
need not preserve the number of assignments. We therefore retain the
original constraints when adding entailed consequences.

## 4. Closest prior work for joint CNF and XOR reasoning

These works guide the next inference and certificate design. The intended
contribution here is a small, audited implementation and a precise account
of its limits, not a claim to invent mixed SAT reasoning.

| Primary work | Relevant result | Consequence for this lab |
|---|---|---|
| Laitinen, Junttila, Niemelä, [*Conflict-Driven XOR-Clause Learning*](https://arxiv.org/pdf/1407.6571), SAT 2012; extended version 2014, Sections 3–7 | DPLL(XOR) combines CNF search with an XOR module that produces clausal explanations for implications and conflicts. Parity explanations can also justify learned XOR clauses. | A clause obtained by falsifying assumptions, propagating binary clauses, and detecting a parity conflict is a restricted instance of established explanation-based learning. Polynomial proofs on special families do not give a deterministic polynomial proof search on all inputs. |
| Soos, Gocht, Meel, [*Tinted, Detached, and Lazy CNF-XOR Solving and Its Applications to Counting and Sampling*](https://pmc.ncbi.nlm.nih.gov/articles/PMC7363182/), CAV 2020 | Integrates Gauss–Jordan reasoning with CDCL, with careful CNF detachment and lazy generation of explanation clauses. | Retain enough provenance to explain an XOR step. Removing a CNF clause requires an actual implication argument. The paper's performance improvements and counting applications do not supply a worst-case polynomial SAT bound. |
| Gocht, Nordström, [*Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs*](https://arxiv.org/pdf/2209.12185), AAAI 2021; full version 2022, Section 4 | Encodes parity reasoning using pseudo-Boolean inequalities and extension variables; certifies derived XORs and reason/conflict clauses. | Keep discovery and checking separate. A checked proof certifies the particular result, not the entire solver implementation or its runtime. Our small native certificate is not a claim to implement VeriPB or DRAT. |
| Ben-Sasson, Wigderson, [*Short Proofs Are Narrow—Resolution Made Simple*](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf), JACM 2001, Section 8 | Enumerating resolution consequences up to width `w` yields an `n^{O(w)}` proof-search bound; width requirements can grow with the instance. | A fixed width can make a closure computation polynomial while leaving it incomplete. Resolution-specific lower bounds need a separate applicability or simulation argument before being transferred to an XOR-enhanced calculus. |
| Beame, Sun, [*Extending CDCL to Disjunctions of Parity Equations*](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2026.5), SAT 2026 | CDCL(⊕) branches on parity equations, propagates algebraically, and learns disjunctions of parity equations. It polynomially simulates Res(⊕) with **nondeterministic decisions and restarts**, and includes LRUP(⊕) proof logging and a prototype. | This is a stronger, recent baseline. The simulation compares proof systems; it does not provide the needed deterministic method for finding short proofs, nor polynomial-length proofs for every UNSAT input. |

The last paper was published July 16, 2026. Treating all mixed reasoning as
an unexplored alternative to existing SAT research would miss both the older
explanation framework and this recent stronger calculus.

## 5. A small mixed inference we can check completely

Here is the precise local rule, stated independently of any implementation.
Let `h_1,...,h_s` be distinct variables and suppose the input entails

\[
 \bigoplus_{i=1}^s h_i=b.
\]

For each `i`, take an input or already justified binary clause

\[
 \ell_i\lor q_i,
\]

where `q_i` is either `h_i` or `not h_i`. Set `v_i=1` in the first case and
`v_i=0` in the second. If

\[
 \bigoplus_i v_i\ne b,
\]

then the mixed input entails

\[
 \ell_1\lor\cdots\lor\ell_s. \tag{1}
\]

**Proof.** If (1) were false, all `ell_i` would be false. Their binary
premises force every `q_i` true, hence `h_i=v_i` for every `i`. That violates
the given parity equation. Therefore every model satisfies (1).

This is a restricted XOR conflict explanation under failed assumptions.
It uses established reasoning; its value here is that premises and signs
can be checked with a very small certificate. A learned unit is the
single-literal special case. For multiple source literals it is more
precise to say a failed-assumption clause than ordinary single-literal
probing.

For the lab's [3SAT bridge](two_cnf_xor_reduction.md),

\[
 (a\lor u)\land(b\lor v)\land(c\lor w)
 \land(u\oplus v\oplus w=0)
 \quad\Longrightarrow\quad a\lor b\lor c.
\]

The forced bits are `1,1,1`, whose XOR is `1`. This recovers the source
clause despite the [CNF-only affine-hull barrier](parity_cuts.md), because
the proof now uses the XOR premise jointly. Recovering an arbitrary original
3SAT formula also recovers its original unresolved difficulty.

A certificate should name the binary premise indices, the signed helper
literals, the derived clause, and a combination of previously justified
XOR rows when the premise row is derived. Checking XOR provenance means
XORing those rows, not trusting the searcher's Gaussian elimination result.
Repeated source literals can be removed. Complementary source literals
make the conclusion tautological. Empty rows and contradictory constant
rows need explicit conventions. Helper freshness is unnecessary for this
semantic proof, though a particular recognizer may require it.

## 6. Polynomial preprocessing is not polynomial complete search

Suppose a recognizer uses a polynomial-size family of explicit rows, each
with at most fixed `w` variables. If each row variable has at most `m`
eligible binary premises, the direct choice enumeration costs at most
`m^w` per row, followed by polynomial-time checks. This is polynomial for
fixed `w`. Unrestricted row width, arbitrary choices of row combinations,
or unbounded nested probing can reintroduce exponential search.

Likewise, the number of normalized non-tautological clauses of width at
most `w` over `n` variables is

\[
 \sum_{j=0}^{w}2^j\binom nj.
\]

A monotone closure over this fixed-width universe, with polynomially many
candidate-rule checks per round and duplicate elimination, is polynomial
for fixed `w`. That counting argument proves termination and a cost bound,
not refutational completeness. Failure to find a contradiction means that
this procedure has not refuted the input. It does not mean SAT. If a full
enumeration solver is used as fallback, its exponential factor must remain
in the overall complexity statement.

There are three separate quantifier issues:

- A short explanation for one inference does not imply short refutations
  for all UNSAT inputs.
- The existence of a short refutation does not supply a deterministic,
  polynomial-time way to find it.
- A lower bound against this recognizer, a particular table representation,
  or resolution alone does not exclude all polynomial-time algorithms.

## 7. Decisions for this phase

The literature supports two concrete directions: implement the small joint
clause rule with independently checkable provenance, and implement an exact
finite signature-sum specialization with explicit dependence checks and
measured table sizes. Both can be verified without assuming the entire ETH
manuscript or its formalization is correct.

External asymptotic claims remain attributed and pinned. Local correctness,
cost bounds, counterexamples, and experiment results remain separate. A
successful example should be followed by a parameterized failure analysis
of the same algorithm; it should not be promoted to a statement about all
SAT solvers. The next theorem needed for `P = NP` would still be a uniform
polynomial bound covering all instances and every step of the algorithm,
including the search for its structural decomposition.

## Ordered frontiers and linear codes

The phase-five bound uses the dimension of the intersection of the prefix and suffix difference spans. Its rank expression is the connectivity function of the represented difference vectors in the convention `r(P)+r(S)-r(P+S)`; vectors from one group must stay together here. Navin Kashyap, [*Matroid Pathwidth and Code Trellis Complexity*](https://doi.org/10.1137/070691152), relates matroid pathwidth to the minimum trellis state complexity of linear codes. Those ordering results concern linear codes; they do not directly prove lower bounds on the reachable nonlinear supports in this project. The [grid proof](affine_frontier.md) instead constructs mutually distinguishable prefix sums with actual suffix completions in the lab's own 3SAT image.

## Graphic matrices and the limits of this use of matching

Robert E. Bixby and Donald K. Wagner, [*An Almost Linear-Time Algorithm for Graph Realization*](https://doi.org/10.1287/moor.13.1.99), construct a tree that realizes a binary path matrix or recognize that none exists. On a basis of the pair differences, that is exactly the graph-realization subproblem of our ternary supports. See the [full equivalence and Fano certificates](graphic_gauge.md) and [CMR's interface](https://discopt.github.io/cmr/graphic.html). Polynomial recognition of this representation does not decide all XOR-choice instances. Our [universality construction](binary_minor_universality.md) applies specifically to residual pair differences of the lab's existing sparse 3SAT bridge. Our [punctured-flat method](hole_flats.md) instead uses exact fiber sizes and conditional exclusion counts and derives its limits independently. We do not assert priority for these algebraic identities or the use of conditional expectations.
