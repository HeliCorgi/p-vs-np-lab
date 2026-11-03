# Audit of the `openai/math` subexponential SAT endpoint

## Status and scope

This is a source-level audit of family 378 at the immutable upstream commit
[`4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae).
It checks the published theorem's quantifiers, input and machine definitions,
selected proof connections, and a numerical schedule used by the construction.
It does **not** constitute an independent rebuild of the complete upstream
dependency graph, successful comparator run, or transitive axiom audit. Those
are separate reproducibility gates. Reading a theorem declaration and proof
text is weaker evidence than replaying the proof with the pinned dependencies.

The actual, dated CI attempts are recorded separately in
[`results/upstream_math_audit.json`](../results/upstream_math_audit.json), with
the source pin, harness commit, run links, observed outcome, and scope. A failed
environment setup or an unfinished bounded build is not a rejected proof.
This source-audit note should not be read as a successful kernel replay.

The selected definitions do not reveal a trivial change of SAT, an
input-dependent machine, an oracle hypothesis at the endpoint, or a unit-cost
arithmetic loophole. This is a limited negative finding, not a certification of
every dependency. The result is relevant enough to investigate seriously; it
cannot be treated as a practical solver or a P versus NP solution on this
inspection alone.

| Upstream item | What it says | Scope of this audit |
|---|---|---|
| [Family 378 description][family] | Exact fixed-width counting, subexponential time, polynomial visited tape space | Compared with the actual statement and machine definitions |
| Manuscript title, “The Exponential Time Hypothesis is False” | A proposed refutation of ETH | The title is a claim, not an independent verification result |
| [`SqrtLogSpace.exact_count_and_sat`][final] | One fixed primitive machine for each fixed clause width, with measured traces | Quantifier order and output/time/space contract inspected |
| [Comparator challenge][challenge] | An independent target statement, ending in `by sorry` | This is the challenge specification; the solution has a different module |
| [Comparator configuration][config] | Selects the solution theorem and permitted axioms | Configuration inspected; successful execution is not claimed here |
| Finite fallback and parameter schedule | A fixed finite table below an existential cutoff | Operational limitations and an exact necessary scale calculated |

## 1. What the endpoint actually quantifies

For each fixed integer \(k\geq2\), the theorem has the following order:

\[
\exists M,\ t_{\rm count},t_{\rm answer},\ C,A,S>0,\ d,e\in\mathbb N_{>0},
\quad
\forall n\in\mathbb N,\ \forall F\in\operatorname{CNF}(\operatorname{Fin}n),
\quad
\operatorname{WidthAtMost}(k,F)\Longrightarrow\exists T,z,\ldots
\]

Here the machine, its output tapes, and all constants are chosen **before**
\(n\) and \(F\). They may depend on fixed \(k\). There is no density condition
at this endpoint, and no eventual-input-size qualification: the finite fallback
covers the small cases. This is the required uniformity in the input size for
fixed-width SAT. A separate effective procedure that prints the machine from
arbitrary \(k\) is not what this quantifier order states, nor is it needed to
specialize the existence claim to 3-SAT. See [the actual theorem][final].

For every valid canonical formula, the conclusion includes all of the
following, for the **same execution**:

1. An actual `Computation.Trace` from the initialized input tape to a final
   configuration after \(T\) primitive steps.
2. A count tape containing `countWord (SAT.count F)`, together with a theorem
   that binary decoding returns exactly `SAT.count F`.
3. A separate answer tape and halting state containing the Boolean test
   `0 < SAT.count F`.
4. A count word of length at most \(n+1\).
5. A time bound, and a polynomial visited-space bound for **every execution
   prefix**, not only the final configuration.

Writing \(L=\texttt{Encoding.formulaBitLength }F\), the exact time expression is

\[
T\leq C(L+1)^d\,2^{A\,g(n)},\qquad
g(n)=\frac{n\,[\ln\ln(n+16)]^2}{\sqrt{\ln(n+16)}}.
\]

The space expression is \(S(L+1)^e\). The logarithms in this expression are
natural logarithms; the small-input shift is 16. These are explicit definitions
in [`SqrtLog/StatementScale.lean`][scale], not inferred asymptotic notation.
The square on \(\ln\ln(n+16)\) must not disappear when summarizing the formal
claim.

The family description also presents a sharper manuscript bound with one
\(\log\log n\) factor, and a fixed-linear-density refinement without that
factor. Those claims are distinct from the squared-loglog formal endpoint
audited here. We do not promote a manuscript refinement to a checked Lean
theorem by citing the weaker endpoint. See [family 378][family].

## 2. Input and cost semantics

### SAT has the ordinary Boolean meaning

Variables are elements of `Fin n`; assignments are functions `Fin n → Bool`.
A literal contains a variable and a polarity. A clause is a finite set of
literals, and a CNF is a finite set of clauses. Satisfaction means at least one
true literal in every clause. Counting ranges over all assignments to the
declared \(n\) variables, including unused variables. The independently expanded
statement in [`StatementCanonical.lean`][canonical] makes this meaning visible
without trusting the names of the abbreviations.

The endpoint promises correctness on `Encoding.encodeCNF F`. It does not by
itself give a rejection convention for arbitrary malformed bit strings. This
is a valid-input contract; parsing and canonicalizing ordinary SAT input is a
separate, polynomial operation.

The encoding uses unary natural-number fields and canonical ordering of finite
sets. Unary fields should be charged, but they do not hide exponential padding
here: fixed-width formulas have a polynomial relation between canonical bit
length and declared \(n\) plus clause count. The upstream file
[`SqrtLogSpace/Statement.lean`][statement] explicitly transports the bound to
\((n+F.\mathrm{card}+1)^{O_k(1)}2^{O_k(\rho(n))}\), where

\[
\rho(n)=\frac{n\,[\log_2\log_2 n]^2}{\sqrt{\log_2 n}}.
\]

The theorem `exact_count_eth` in [the final module][final] uses that transport.
Thus the large-input conclusion is not contingent on counting only a tiny
fraction of a padded input.

### The endpoint measures primitive tape steps

[`Computation.lean`][computation] defines a finite number of tapes, a finite
control state type, Boolean or blank tape symbols, and a fixed transition
function. A primitive transition selects a tape and performs a bounded action
such as writing a symbol, moving its head by one cell, or halting. It is not a
unit-cost operation on an arbitrarily large integer or a semantic SAT query.
`Trace` is an inductive iteration of that transition relation.

The space-aware endpoint in [the final module][final] wraps the primitive
configuration in `LocatedCfg`.
Its prefix condition bounds visited tape cells, including cells traversed
during the computation. The initialized configuration contains the explicit
input word and blank work tapes. There is no per-input advice tape in the
statement.

The finite transition function can nevertheless be enormous. In the usual
fixed-machine complexity convention its size is a constant, independent of
the input. That convention is mathematically relevant below and is not a
claim of practical implementability.

## 3. Specification, proof chain, and trust

The [comparator challenge][challenge] deliberately ends with `by sorry`: it is
the proposition against which the submitted proof is compared. Treating that
line as a discovered hole in the solution would inspect the wrong module.
The [JSON configuration][config] points to
`OAI.Algorithms.SubexponentialSAT.Main` and names
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` as the
solution theorem. It permits `propext`, `Quot.sound`, and `Classical.choice`.
That list is a policy for a successful comparison, not an observed list of
axioms from a run performed in this audit.

The inspected construction follows this chain:

| File | Role visible in the source |
|---|---|
| [`SqrtLogSpace/Final.lean`][final] | Uses `compiled_exact_count_and_sat` to produce the primitive-machine endpoint |
| [`SqrtLogSpace/NativeLargeEntry.lean`][large] | Assembles preprocessing, tree/leaf bounds, the native program, and a size cutoff |
| [`SqrtLogSpace/NativeLeafContract.lean`][contract] | Supplies a `uniform_contract` for the particular installed leaf implementation |
| [`SqrtLogSpace/NativeLeafProgram.lean`][leaf] | Installs concrete high-query `marked` and `accepted` programs within the leaf command |
| [`SqrtLogSpace/FiniteFallback.lean`][fallback] | Supplies a fixed finite counting table for input sizes below the cutoff |

In `Final.lean`, the compiled program has type
`BitProgram.Program 80 1220 labels`: 80 Boolean registers and 1220 stacks at
that intermediate level, with a finite number of labels chosen by the
construction. It is then compiled to the primitive tape model. The program is
`Native.countingProgram cutoff k (NativeLeafProgram.command k)`.

Local evaluator contracts occur inside the proof, but the inspected endpoint
does not assume such a contract from the caller. `NativeLargeEntry.run` obtains
it from `NativeLeafContract.uniform_contract` for the installed command. This
removes one possible endpoint-level oracle loophole; it does not replace an
audit of every theorem proving the contract.

A complete independent check still needs to pin the Lean toolchain and
dependencies, replay the intended target, compare the independent statement,
and inspect the actual transitive axioms. It also needs a mathematical reading
of the key reductions, rather than relying only on filenames and signatures.
No success at those broader gates is asserted in this source-audit note.

## 4. The cutoff is not a usable small constant

### Exact schedule

[`SqrtLogSpace/Asymptotics.lean`][asymptotics] defines integer parameters

\[
\lambda(n)=\lceil\log_2n\rceil,\qquad
\nu(n)=\lceil\log_2\lambda(n)\rceil,\qquad
s(n)=\left\lfloor\frac{\lfloor\sqrt{\lambda(n)}\rfloor}{\nu(n)^2}\right\rfloor.
\]

For \(n\geq20\), the denominator is nonzero. The file proves the exact
equivalence

\[
a\leq s(n)\quad\Longleftrightarrow\quad a^2\nu(n)^4\leq\lambda(n).
\]

The large-input assembly specifically needs \(s(n)\geq2\), so
\(\lambda(n)\geq4\nu(n)^4\) is necessary. At a fixed integer \(\nu\), the
allowable \(\lambda\) interval is
\(2^{\nu-1}<\lambda\leq2^\nu\). Checking those integer intervals gives the first
feasible value

\[
\nu=19,\qquad \lambda=4\cdot19^4=521{,}284,
\qquad n_{\rm first}=2^{521283}+1.
\]

This number has approximately 156,922 decimal digits. The calculation can be
made with small exact integers; it does not require constructing that value of
\(n\). The first positive schedule value is already at
\(\lambda=65536\), or \(n=2^{65535}+1\), within the \(n\geq20\) regime.

The schedule is **not monotone**. At a ceiling-log boundary its denominator
jumps. Exact examples are:

| \(\lambda\) | \(\nu=\lceil\log_2\lambda\rceil\) | \(s\) |
|---:|---:|---:|
| 521,283 | 19 | 1 |
| 521,284 | 19 | 2 |
| 524,288 | 19 | 2 |
| 524,289 | 20 | 1 |
| 639,999 | 20 | 1 |
| 640,000 | 20 | 2 |
| 1,048,577 | 21 | 2 |

Consequently, the **first possible** value above is not a threshold after which
every larger input satisfies the requirement. For this one schedule condition,
\(\lambda\geq640000\) does suffice: the rest of the \(\nu=20\) interval works,
and for \(\nu\geq21\), the interval's lower endpoint exceeds \(4\nu^4\).
For example, \(2^{20}>4\cdot21^4\), and
\(((\nu+1)/\nu)^4\leq(22/21)^4<2\) propagates that inequality inductively.
This elementary sufficient bound for **one condition** is still not the full
construction's cutoff.

### The actual cutoff has additional obligations

[`NativeLargeEntry.run`][large] obtains an eventual lower bound on the schedule
from an asymptotic limit, and separately obtains a leaf threshold. Its source
contains the following structure:

```lean
obtain ⟨..., Nleaf, ..., hleaf⟩ := NativeLeafContract.uniform_contract ...
obtain ⟨Ns, hs⟩ := Filter.eventually_atTop.mp
  (sparsifySchedule_tendsto.eventually (Filter.eventually_ge_atTop 2))
let cutoff := max 20 (max Nleaf Ns)
```

Here `Ns` must work for **all** larger input sizes, and `Nleaf` has independent
requirements. Neither their chosen numerical values nor the complete runtime
constants were extracted in this audit. The \(521284\) calculation is a
necessary scale observation, not the value of `cutoff`, not a sufficient
condition for the whole proof, and not a measured running time.

### Why the finite fallback is mathematically different from an executable

[`FiniteFallback.lean`][fallback] defines noncomputable `inputBound`,
`tableCount`, `outputTable`, and `countProgram`. For a **fixed** cutoff \(B\),
the set of canonical formulas with \(n\leq B\) is finite. The construction
places their exact output words into a fixed finite transition table, before
the input is supplied. The actual scanner then consumes an input and emits
the associated count bits. The proof charges the runtime scan and output.

This does not constitute input-dependent advice: \(B\) and the table are fixed
before all inputs. Nor does `noncomputable` alone invalidate an existence
theorem for a finite machine. Every particular finite table describes a
computable finite-control machine. However, a theorem establishing existence
of such a table is not a practical method for materializing it, and its size
is not charged as per-input runtime under the fixed-machine convention.

Together with the scale calculation, this explains why copying this endpoint
into our repository would not produce a usable SAT executable. The useful
immediate assets are the definitions, proof interfaces, algorithmic ideas,
and independently checkable components; extracting a workable implementation
would require additional, explicit choices and bounds.

## 5. Consequences for this lab

If the full proof replay and statement comparison succeed, and the definitions
have the intended interpretation, the fixed-\(k\) endpoint gives
\(2^{o(n)}\operatorname{poly}(n+m)\) exact counting and decision. In particular,
the 3-SAT instance would contradict ETH. This is a conditional implication
from the inspected statement, not an assertion that this note settles the
status of ETH.

It does **not** establish \(\mathrm P=\mathrm{NP}\). The displayed upper bound
contains a sublinear but much larger than logarithmic exponent; it supplies
no fixed polynomial bound. Conversely, an upper bound of this form is not a
lower bound on the constructed algorithm and does not prove
\(\mathrm P\ne\mathrm{NP}\). Our own joint CNF+XOR inference remains subject
to its explicit residual exponential families, independently of the upstream
claim's eventual validation.

The appropriate reuse is therefore to keep three pieces of evidence separate:
the upstream source claim, an independently reproduced formal check, and an
executable solver measured against original formulas. The first has been
inspected here; the other two must carry their own evidence.

[family]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/378.md
[challenge]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/SubexponentialSAT.lean
[config]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/SubexponentialSAT.json
[final]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean
[scale]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/StatementScale.lean
[canonical]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/StatementCanonical.lean
[statement]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Statement.lean
[computation]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/Computation.lean
[large]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLargeEntry.lean
[contract]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafContract.lean
[leaf]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafProgram.lean
[fallback]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FiniteFallback.lean
[asymptotics]: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Asymptotics.lean
