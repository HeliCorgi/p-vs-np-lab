# Reusing and auditing openai/math

## Follow-up prompted by the ETH article (2026-11-09 JST)

The [DataCamp article](https://www.datacamp.com/blog/ai-exponential-time-hypothesis)
was read and checked against the primary source below. The current upstream
family-378 scope still distinguishes the sharper manuscript bound from the
squared-loglog Lean bound. Neither statement is a polynomial-time SAT bound.
The historical incomplete local kernel-replay record remains unchanged.

This continuation executes a new [finite repair audit](../results/eth_polynomial_repair.json),
with its all-size arguments and source attribution in the
[implementation](../experiments/eth_polynomial_repair.py). It optimizes the
auxiliary matrix `V*f(W)` over all degree-bounded rational polynomials in
51 small parameter cases, using 4,591 interpolation candidates. For `r=4`,
`Q=12`, degree two, `f(j)=5/3-(2/3)*(j-5)^2` matches levels `3,4,6,7`.
The correction rank is `104521901510656`, compared with `108217056710656`
for the best consecutive interpolation or constant: about 3.4% smaller.
This finite optimum follows from exhaustive interpolation, with independent
rational and dense-matrix checks. It does not optimize every possible matrix,
establish novelty, or meet the complete SAT construction's small-tail target.

Computing the rank through `Q+1` spectral multiplicities avoids a dense matrix
but does not evaluate an input CNF. The audit shows that keeping both explicit
coordinate/Taylor enumerations has superpolynomial cost for every parameter
choice in its stated domain. Moreover, retaining Step 4's sufficient balancing
conditions forces a variable group of size at least `sqrt(2n)` and the overview's
scheduled Taylor order `Omega(n/log n)`, even with implicit rank computation. These conditions could
be replaced by a new construction; no impossibility for all constructions,
the sharper appendix, or all SAT algorithms follows. No general polynomial
algorithm or new Lean theorem has been obtained.

## 1. What was actually inspected

This investigation is pinned to OpenAI's public repository at commit
[4eaee87548250b2682affda7d05d947c05554bae][upstream], committed on
2026-10-30. Its root tree is
`71e8eaa37259d11418fe4ee382a0f82b91ea973e`.
The upstream [README][readme] describes **721 manuscripts in 373 families**.
We independently counted 373 family headings and 721 distinct linked
preprint directories in the complete [catalogue][catalogue], matching those
README figures. The underlying preprint tree contains 751 directories;
30 are not linked from the current catalogue, so the directory count must
not be mistaken for the current manuscript count.

This is a collection of mathematical research manuscripts and selected Lean
formalizations, not a ready-to-run SAT package or a replacement for Mathlib.
The upstream README calls the manuscripts raw research data, reports different
levels of verification, and says the underlying internal model is unreleased.
The reasoning summaries cover ten families; there is no family 378 summary
in the pinned directory. They are not an available model, solver, or checker.

The inspection covered the root tree, complete catalogue, Lean configuration
and manifest, complete SAT source subtree, selected manuscript source, formal
endpoints, comparator specification, and relevant licensing. It did **not**
review all 721 manuscripts or independently kernel-check all formalizations.

The complete SAT subtree has Git tree SHA
`959444ea69d08eecc94480ece6621be36947dd09`.
The recursive tree response was not truncated. It contains **3,977 Lean files,
35,509,858 source bytes**, distributed as follows:

| Location below `lean/OAI/Algorithms/SubexponentialSAT/` | Lean files |
| --- | ---: |
| Root | 1,258 |
| `SqrtLog/` | 2,004 |
| `SqrtLogSpace/` | 327 |
| `Subexp/` | 388 |

The GitHub contents endpoint returned only the first 1,000 entries; that
partial response was replaced with the complete subtree inventory.
All files in this subtree are Lean sources. No binary solver or compiled
proof artifact is included there. The pinned Lake file has no SAT executable
target, and the repository's releases endpoint was empty when inspected.

A compact [source snapshot](../third_party/openai_math/README.md) retains the
relevant scope statements, comparator challenge, actual endpoint source,
license, and measurement lemma. Its
[manifest](../third_party/openai_math/manifest.json) records exact upstream
paths, commit, Git blob SHA-1 values, local raw-byte SHA-256 values, extraction
intervals, and transformations. Thirteen unchanged source copies were checked
against their upstream Git blob hashes; two excerpts are explicitly marked.
The large proof dependency tree is not vendored into this lab.

## 2. Selection: what helps this project

| Material | Relevance and action |
| --- | --- |
| Family 378, *The Exponential Time Hypothesis is False* | Highest priority. Inspect the exact theorem and representation, reproduce its formal endpoint separately, and extract the finite measurement identity for grouped XOR counting. |
| Its measurement-separation lemma | Direct mathematical reuse. The identity has explicit hypotheses and costs and can be checked independently of the proposed asymptotic breakthrough. An attributed source excerpt is included. |
| Comparator challenge and axiom configuration | Direct audit reuse. Keep the intended statement separate from the implementation, inspect definition correspondence, and retain a precise axiom whitelist. |
| Family 102, Unique Games and approximation thresholds | Useful reduction and quantifier reference. Its scope includes polynomial reductions from binary 3SAT with explicit gap parameters. It does not establish P versus NP. A scope snapshot is included; its reductions have not been ported. |
| Families 103, 104, 106, 112, 117, 126, 133, 135, 136, 192, 274 | Catalogue-level research leads: derandomization, games, approximation, circuit or representation lower bounds, and Boolean structure. No theorem from these families is assumed by our solver. |
| Other mathematical and physical manuscripts | No concrete dependency for the present XOR/CNF experiments was identified. They were not copied merely to increase imported material. |
| Internal model and reasoning summaries | Methodological context only. The internal model is unavailable; released summaries do not supply an executable research agent or SAT algorithm. |

For example, family 112 concerns depth-three OR–AND–OR circuits, family 135
homogeneous depth-five algebraic circuits, and family 274 constant-depth
quantum circuits. Even accepting their stated results would not make them
lower bounds for unrestricted deterministic polynomial-time computation.
An ETH-dependent claim encountered in family 133 must retain that assumption;
it cannot be combined uncritically with family 378's proposed refutation.
These are classifications of catalogue statements, not independent
validations of those results. [Catalogue][catalogue]

### Licensing

The actual root `LICENSE` and `lean/LICENSE` contain Apache License 2.0 and
have the same Git blob SHA,
`261eeb9e9f8b2b4b0d119366dda99c6fd7d35c64`.
No additional license or NOTICE file was present in the selected SAT subtree
or selected paper directory. Copied files retain their contents and
provenance; excerpts have prominent modification notices and the upstream
license is included. Dependency projects such as Mathlib and Comparator
remain separate projects with their own licenses.

## 3. Family 378: distinguish the three runtime statements

The upstream [formalization scope][scope378] explicitly separates these
claims. Here `k` is a fixed maximum clause width, `n` the number of declared
variables, `m` the number of clauses, and `L` the canonical encoding length.

| Scope | Claimed exact counting time |
| --- | --- |
| Lean endpoint | \((L+1)^{O_k(1)}2^{O_k(n(\log\log n)^2/\sqrt{\log n})}\) |
| October 25 manuscript, arbitrary clause count | \((n+m)^{O_k(1)}2^{O_k(n\log\log n/\sqrt{\log n})}\) |
| Manuscript, fixed density \(m\le Dn\) | \((n+m)^{O_{k,D}(1)}2^{O_{k,D}(n/\sqrt{\log n})}\) |

The formal endpoint also bounds **all execution prefixes** by polynomially
many visited tape cells, not merely the final output size. The sharper
manuscript bounds must not be reported as the exact theorem checked by
OpenAI's comparator configuration.

If correct, the fixed-width subexponential result would refute the usual ETH.
It would still not supply a polynomial-time algorithm: the displayed
exponent is \(o(n)\), but it is not bounded by \(O(\log n)\).
Nor does a \(2^{o(n)}\) bound automatically survive an arbitrary
polynomial-size reduction. This lab therefore uses separate
[solution criteria](solution_criteria.md) for P versus NP.

### What the Lean endpoint actually states

The [challenge specification][challenge] defines finite Boolean clauses,
assignment semantics, exact counting, canonical input encoding, a primitive
finite machine, transition traces, and visited tape intervals. The canonical
integer encoding is unary, with sorted clauses/literals, so the declared
variable count contributes to `L`.

The quantifier order is substantive:

\[
 \forall k\ge2,\quad
 \exists M,C,A,d,S,e,\quad
 \forall n,F\text{ of width at most }k,\quad
 \text{correct run of }M\text{ with the stated bounds}.
\]

The machine and constants are chosen before the input formula. This does not
permit a different answer-containing machine for every input.
The actual [endpoint source][final] constructs a finite program, checks its
exact binary count, SAT bit and halt state, and connects that program to the
primitive machine trace.

The additional theorem `exact_count_eth` converts the canonical bit-length
bound to a polynomial in `n + F.card + 1`. Its proof uses a fixed-width
encoding estimate with coefficient `8*k + 7` and doubles the polynomial
exponent. The encoding conversion is part of the source theorem.

The solution [Main module][main] imports both the earlier `SqrtLog` execution
endpoint and the `SqrtLogSpace` endpoint. The selected theorem is
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`.

The [comparator configuration][config] permits only `propext`, `Quot.sound`,
and `Classical.choice`, has no definition holes, and sets
`enable_nanoda: false`. The `sorry` in the challenge file is intentional:
it declares the proposition the independent solution must establish.
It is not an unproved line inside the endpoint implementation.
Conversely, a configuration that asks for permitted axioms is not evidence
that the actual check has passed.

**Local evidence boundary:** source inspection found a substantive finite
machine specification with appropriate quantifier order and explicit
runtime/space conclusions. This snapshot task did not rebuild the complete
proof or replay the comparator. A separate build's logs and status must be
reported independently. External replication reports and their
qualifications are covered in [prior work](prior_work.md).

## 4. What the paper's algorithm does

The manuscript's body begins with the exact polynomial expression

\[
 \#F=\sum_{x\in\{0,1\}^n}\prod_e\Phi_e(x),\qquad
 \Phi_e=1-\prod_{\ell\in e}(1-L_\ell).
\]

It replaces each variable occurrence by a parameterized rational linear form
\(P_{e,v}(T)\cdot x\), with \(P_{e,v}(0)=\delta_v\).
The resulting univariate sum satisfies \(H(0)=\#F\).
At selected nonzero points, the proposed replacement forms allow small
variable groups coupled through bounded integer measurements.
The count is recovered by truncated Taylor data and rational Hermite
interpolation. The general fixed-width case also requires the paper's
sparsification and sparse-equation reductions. [Manuscript source][paper-source]

The construction must simultaneously control replacement degree, evaluation
points, group sizes, measurement counts, coefficient size, and exact
arithmetic. None of these objects can be assumed to arrive for free.

For the bounded-occurrence overview, put
\(q=\lfloor3nR/Q\rfloor\), with replacement degree `R` and `Q` evaluation
points. Its three enumeration costs are

\[
 \underbrace{\sum_{j=0}^{\min(q,n)}2^j\binom nj}_{\text{Taylor substitutions}}
 \;\underbrace{(2D+1)^{2\tau n}}_{\text{integer measurements}}
 \;\underbrace{2^{2n/r}}_{\text{one group}}.
\]

The overview chooses
\(r=\Theta(\sqrt{\log n}/(\log\log n)^2)\),
\(Q=\Theta(\log n/\log\log n)\),
\(R=\Theta(\sqrt{\log n})\), and
\(\tau=\Theta(1/(r\log n))\), with polynomially bounded measurement
coefficients. This explains the squared-log-log exponent of the body/formal
statement. The sharper appendix uses further contraction arguments.
We extracted the finite measurement lemma; we did not independently validate
every replacement construction, reduction, interpolation, or appendix theorem.

### A finite identity we can reuse immediately

The attributed
[measurement source excerpt](../third_party/openai_math/paper/measurement-separation-excerpt.tex)
contains the formal lemma and its hypotheses.

Partition the variables as \(S_1\sqcup\cdots\sqcup S_r\).
For each group choose an integer matrix \(C_g\).
Assume factor \(A_g\) is invariant under changes in another group that
preserve that group's measurement: for \(h\ne g\),

\[
 A_g(x+\xi)=A_g(x)
 \quad\text{if }\operatorname{supp}\xi\subseteq S_h,\ C_h\xi=0.
\]

Put \(X_g(y_g)=\{u\in\{0,1\}^{S_g}:C_gu=y_g\}\), and choose a representative
\(\bar x_g\) of each nonempty fiber. Then

\[
 \sum_x\prod_g A_g(x)
 =
 \sum_{(y_1,\ldots,y_r)}
 \prod_g\left[
   \sum_{u\in X_g(y_g)}
   A_g\!\left(u+\sum_{h\ne g}\bar x_h\right)
 \right].
\]

Empty fibers contribute zero. Every Boolean assignment has exactly one
measurement tuple; each tuple's assignments form a Cartesian product of
fibers; invariance validates the representative substitution.
Distributivity proves the identity. No complexity conjecture is used.

If each integer row has absolute coefficient sum at most `D`, with `c` rows
in total, the paper's scanning implementation examines at most

\[
 2(2D+1)^c\sum_g2^{|S_g|}
\]

Boolean vectors. Per vector it charges at most one factor evaluation,
polynomial additional bit work, and constant many ring operations. Its space
statement excludes the evaluators' storage and ring elements; those must be
charged separately in an application.

The coefficient bound matters. A single integer row
\((1,2,4,\ldots,2^{b-1})\) distinguishes all \(2^b\) Boolean assignments.
Small rational rank alone does not produce a small measurement domain.
This warning appears immediately before the source lemma.

### Our GF(2) specialization

For group-local CNF factors \(F_g\) and a global XOR system \(Ax=b\),
let \(A_g\) contain the columns belonging to \(S_g\), and build

\[
 T_g(s)=\#\{u\in\{0,1\}^{S_g}:F_g(u),\ A_gu=s\}.
\]

The exact full count is

\[
 \sum_{s_1\oplus\cdots\oplus s_r=b}\prod_gT_g(s_g).
\]

This is the same finite fiber decomposition specialized to Boolean
signatures and integer counts. The local implementation is described in
[signature counting](signature_counting.md), with
[source](../src/pnp_lab/signatures.py),
[tests](../tests/test_signatures.py), and an
[experiment](../experiments/signature_counting.py).
Its algorithm enumerates local assignments, buckets contributions, and
combines tables by XOR convolution. CNF factors must be group-local;
otherwise their cross-group dependence must be represented and checked.

This specialization does not implement the upstream replacement construction
or inherit its subexponential theorem. It has visible costs: local assignment
enumeration, table construction, signature support, table joins, and integer
arithmetic. With `q` XOR output bits, a full table may have \(2^q\) entries.
A group of `b` variables with identity measurement has exactly \(2^b\)
signatures. A single group containing all variables leaves \(2^n\) local
assignments. These are limits of this table representation, not lower
bounds for all SAT algorithms.

## 5. Why this is not a practical solver download

The inspected `SqrtLogSpace/NativeLeafProgram.lean` uses a
`noncomputable section`. `FiniteFallback.lean` constructs its finite
small-input transition table via noncomputable finite-domain definitions.
`NativeLargeEntry.run` obtains a fixed cutoff from asymptotic existence
lemmas before reading any formula. The pinned
[large-input entry source](../third_party/openai_math/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLargeEntry.lean)
is included in the snapshot. This is compatible with the existence
of a fixed finite machine, but does not expose a ready `#eval` implementation
or practical DIMACS command.

Even the formal large-input schedule is extremely conservative.
The separate adversarial audit found that the required
`sparsifySchedule n >= 2` first holds, for `n >= 20`, at
\(n=2^{521283}+1\).
Set \(\lambda=\lceil\log_2 n\rceil\),
\(\nu=\lceil\log_2\lambda\rceil\) and require
\(\lfloor\sqrt{\lambda}\rfloor\ge2\nu^2\).
The first feasible pair is \(\lambda=521284,\nu=19\). The exact definitions
are retained in the pinned
[Asymptotics source](../third_party/openai_math/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Asymptotics.lean),
and [the parameter experiment](../experiments/upstream_parameters.py)
recomputes this threshold using integer arithmetic. The schedule is not
monotone: it drops below two again at \(\lambda=524289\).
Thus first feasibility is not the final eventual cutoff; that cutoff remains
uninstantiated and can be larger still. This limits practical use without
refuting the asymptotic existence statement.

The reusable pieces are the finite factorization identity, accounting of
signature domains, precise machine specification, and statement/implementation
audit structure. A separately engineered solver needs explicit parameters,
constructive implementation, practical fallback, and its own cost analysis.

## 6. Rebuilding only the relevant upstream target

The separate [execution record](../results/upstream_math_audit.json) reports
what our CI actually did. It distinguishes harness setup, the endpoint build,
transitive axiom inspection, and the unrun comparator. The source-snapshot
hash checks are not evidence that any of those proof gates succeeded.

Upstream uses `leanprover/lean4:v4.34.1` with Mathlib pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The lab's `Formal/` project retains its Lean 4.19.0 toolchain.

The upstream [Lean README][lean-readme] recommends building small portions
and documents a possible `vm.max_map_count` failure for the full library.
It provides no runtime estimate for this target. The pinned `.github/` tree
contains a PR-locking workflow, not a build verification workflow.

The full upstream Lake configuration declares many unrelated dependencies
and runs compatibility-patch bootstrap code during configuration elaboration.
A sparse checkout alone does not prevent those clones.
A bounded audit can use a separately documented minimal Lake harness with
pinned Mathlib and the unchanged transitive source closure of relevant
modules. Such a harness is an adaptation; retain its exact configuration
and source hashes.

This lab's [preparation script](../scripts/prepare_upstream_audit.py) targets
the relevant `SqrtLogSpace.Final` module directly, records the complete
transitive OAI source closure and hashes, and emits an axiom-printing audit
file. Its preparation status is explicitly separate from a successful build
and from comparator validation.

Lean 4.34.1's Lake documentation supports a module-specific target:

```sh
lake build +OAI.Algorithms.SubexponentialSAT.Main
```

This recursively builds imports, which can still be large. A time budget
is an operational limit. A timeout is neither a theorem refutation nor a
successful verification.

The upstream Comparator README instructs installing `comparator`, `landrun`,
and `lean4export`, then running from the Lean project:

```sh
lake update
lake exe cache get
lake env comparator ComparatorChallenges/SubexponentialSAT.json
```

These are upstream instructions, not a claim that this exact stack has
already succeeded here. A controlled harness must preserve its recorded
dependency pins when resolving packages.

The nearest published compatible-version starting points inspected were:

| Component | Pinned starting revision |
| --- | --- |
| Comparator v4.34.0 | `d03acab154d269c06e60e4de7e4cc85deebff94b` |
| lean4export v4.34.0 | `076e8e57707e813375e8f9da8bf989799ace9680` |

Neither inspected tag inventory contained v4.34.1. Rebuilding these sources
under Lean 4.34.1 is an adaptation whose compatibility must be checked.
The Comparator v4.34.0 manifest pins the exporter, although its Lake
declaration says `master`; an indiscriminate update would lose that pin.
Its documented build command is `lake build lean4export comparator`.

The [Comparator documentation][comparator] distinguishes actual sandboxed
checking from its `fake-landrun.sh` development helper.
The helper does not count as a security-isolated audit.
A fresh independent audit preserves the challenge/checking environment
before compiling solution code, uses the documented supported sandbox,
and checks actual exit status and exported axioms.
An ordinary build plus `#print axioms` is useful evidence but differs from
a comparator replay that also checks statement definitions.

## 7. Evidence levels and remaining work

This phase uses the material at three levels, with separate evidence:

1. **Source provenance:** selected files are pinned and content-hashed,
   with the upstream license and marked excerpts.
2. **Finite mathematical reuse:** the signature identity has an independent
   finite proof, explicit preconditions, counterexamples to unrestricted
   compactness, and a locally testable specialization.
3. **Upstream theorem audit:** the large result requires its own
   build/comparator outcome. A source snapshot, catalogue label, external
   reports, and the small specialization do not substitute for that outcome.

A route to P versus NP requires a general polynomial bound on all relevant
construction and counting work, or an unrestricted lower-bound argument.
Neither follows merely from the measurement identity or from refuting ETH.

[upstream]: https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae
[readme]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/README.md
[catalogue]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md
[scope378]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/378.md
[challenge]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/SubexponentialSAT.lean
[config]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/SubexponentialSAT.json
[final]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean
[main]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/Main.lean
[paper-source]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex
[lean-readme]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/README.md
[comparator]: https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md
