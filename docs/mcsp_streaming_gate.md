# Early pruning: a goal-level streaming lower-bound target

2026-11-06 UTC. The user asked to continue toward a complete proof of P=NP
or P≠NP and to abandon unpromising branches early. **No complete proof or
new general lower bound was obtained in this investigation.** The work here
is a source-checked route selection and a reconstruction of known reasoning,
not a new SAT solver or a claimed breakthrough.

The subsequent [direct core attempt](mcsp_update_core.md) supplies a
three-gate counterexample to strict progress by minimum circuit size, an
explicit distinction between prescribed validation and repair search,
and a uniform one-point repair bound. The all-algorithm target is still
unproved.

## Branch decisions before implementation

| Candidate | Mathematical check | Decision |
|---|---|---|
| Add orders or local rewrites to phase 28's shared-DAG solver | Its state lower bound concerns one algorithm and order. Extra rules supply no uniform bound on all inputs. | Stop this development branch unless a new all-input argument is supplied. |
| Replace Boolean circuit zero-testing by ordinary polynomial identity testing | The unsatisfiable formula `x AND NOT x` arithmetizes to `x(1-x)`, a nonzero formal polynomial which vanishes on the entire Boolean cube. | Reject this substitution immediately; no implementation. |
| Use a magnification theorem whose endpoint is only `NP ⊄ NC1` or `EXP ⊄ NC1` | Those conclusions alone do not imply P≠NP. In particular, P=NP does not imply P is contained in nonuniform NC1. | Do not use these endpoints as a solution bridge. |
| Prove a streaming lower bound for search-MCSP that exceeds every polynomial in the circuit budget, in space or update time | McKay–Murray–Williams [MMW], Theorem 1.3, gives a direct implication to P≠NP. | Retain as a precisely stated sufficient target, **not as a proved lower bound**. |
| Prove that search-MCSP intrinsically needs large streaming memory by counting distinguishable prefixes | A small circuit matching the prefix is an unconditional small-space representation, if arbitrary update time is allowed. | Reject this memory-only sub-branch; proof below. |

The polynomial-identity failure does not rule out all algebraic approaches.
It rules out identifying an ordinary polynomial with its Boolean function.
Testing in the quotient by `x_i^2-x_i` would address the semantics, but an
efficient general procedure for that task is the missing work. Phase 27's
sparse-expansion obstruction also cannot be ignored by treating a compact
circuit as an explicitly available multilinear polynomial.

## The selected sufficient target and all its quantifiers

Use ordinary Boolean circuits with AND/OR gates of fan-in two, NOT gates,
and constants. Let n >= 2, N = 2^n, and fix **s(n) = n^2**. Gates, not
truth-table entries, are bounded by s. A circuit has a padded binary
description of length

\[
 \ell(n,s)=O\bigl(s\log(s+n)\bigr)=O(s\log s).
\]

`search-MCSP[s]` takes the N-bit truth table of a Boolean function on n
variables, in **lexicographic input order**, and outputs either a circuit
with at most s gates computing it or `NO` if no such circuit exists.
The parameter n is supplied before the stream; equivalently the length is
known. Finite exceptional lengths can be handled separately.

A deterministic one-pass machine can do internal computation between
successive input bits. It cannot reread the stream. Charge working memory,
initialization, every interval between reads, and final reporting; it cannot
hide a long computation after the last bit. Operations must have an ordinary
bit-cost implementation. This is consistent with [MMW, §2]; their update
bound explicitly also bounds reporting time.

Let S_A(T) be peak memory and U_A(T) the largest initialization, update or
reporting cost on input T. A sufficient **unproved** target is:

\[
\begin{split}
 &\forall A\text{ correctly solving this search problem},\quad
   \forall c\in\mathbb N,\ \forall K>0,\ \forall n_0,\\
 &\qquad\exists n\ge\max(2,n_0),\ \exists T\in\{0,1\}^{2^n}:\\
 &\qquad\qquad \max\{S_A(T),U_A(T)\}>K(s(n)+1)^c. \tag{Target}
\end{split}

The machine is uniform and finite; c and K are independent of the input.
Separate polynomial bounds on S and U can be combined by increasing c
and K. Correct machines halt on all inputs. Finite exceptions can be
absorbed into K, explaining the arbitrary-n_0 form.

One bound for one solver, one exponent, one representation or one fixed
transition rule is insufficient. A lower bound on decision MCSP under the
same resource restrictions would also suffice, since a search solver
decides it. This does not identify the two streaming problems as equivalent.

[MMW, Theorem 1.3] is more general: it permits time-constructible s >= n
and circuit oracles A in PH. The target above fixes s=n^2 and uses **no
circuit oracle**. No claim that ordinary MCSP is NP-complete is required.
The bridge is sufficient; it is not an assertion that this particular
target is equivalent to P≠NP.

## Reconstructing the bridge without an uncharged oracle

Here is a slower but sufficient one-bit version of the prefix merging
argument in [MMW, §§1.2, 4–5]. Unlike their canonical minimum-circuit
routine, this version needs only some circuit within the size budget.
It does not claim their finer total-time bounds.

After reading positions 0 through i-1, maintain either a rejection flag or
a circuit C of size at most s with

\[
        \forall x<i,\quad C(x)=T_x. \tag{Invariant}
\]

Initially take the constant-zero circuit. On reading bit b at position i,
look for a circuit D with at most s gates satisfying

\[
    D(i)=b\quad\land\quad\forall x<i:\ D(x)=C(x). \tag{Repair}
\]

If it exists, replace C by D; otherwise reject and enter a permanent sink.
If C already gives b at i, retaining C is valid. At the end output C if
there has been no rejection.

**Correctness.** Induction proves the invariant. If a circuit for the entire
table exists, it is a witness to every Repair query, because C agrees with
the table on the past prefix. Thus a positive input is never rejected.
Conversely, successful processing through N bits supplies a circuit for
the entire table. At an unsuccessful repair, no circuit within the size
budget agrees even with the prefix, so none can compute the entire table.
Choosing one representative does not discard possible future completions:
Repair compares its past values only, not its unused future predictions.

**Conditional cost.** Consider the decision predicate that Repair has a
witness whose padded description starts with a specified bit string p.
All descriptions have length ell and the query is padded accordingly;
we do not encode a huge witness bound using only log(s) input bits.
The predicate has the form

\[
  \exists D\in\{0,1\}^{\ell}\ \forall x\in\{0,1\}^{n}:
             R(n,s,C,i,b,p,D,x),
\]

where R checks valid encoding, size, prefix p, and the conditions in Repair
in time polynomial in the query length. In particular, it is in Sigma_2^P.

Under P=NP, a universal polynomial-time predicate is decidable in P,
because coNP=P. Existentially guessing D then also gives a P predicate.
Thus this one fixed language, for all n and s, has a polynomial-time
decider under the assumption. First test existence, then recover a padded
description by at most ell prefix queries. This is an ordinary uniform
search-to-decision reduction, not free access to a witness.

Each query has size polynomial in s, there are polynomially many per bit,
and polynomial-time computations use at most polynomial space. Reading,
maintaining the n-bit index, and reporting the circuit also meet these
bounds. Consequently

\[
 \mathrm P=\mathrm{NP}
 \ \Longrightarrow\
 \text{search-MCSP}[n^2]\text{ has polynomial-in-}s
 \text{ space and update/reporting time}. \tag{Bridge}
\]

Taking the contrapositive yields Target => P≠NP. **The bridge is established
reasoning; Target is not established.** [MMW] implements canonical minimum
outputs with Sigma_3-SAT queries and obtains sharper oracle-model bounds.
The use of sequential Sigma_2 prefix queries here is not a claim that the
paper states a different oracle bound. [Modanese, §5] also explicitly uses
Sigma_2 search with output-prefix queries for its merging construction.

## Why prefix counting cannot prove Target

The same representative algorithm is unconditionally implementable with
small memory and very slow updates. Enumerate all valid descriptions D
using an ell-bit counter. Check each candidate by enumerating x<i and
evaluating the two circuits; all past bits are regenerated from C. Store
C, D, their evaluation workspace and the n-bit index, then discard a
failed candidate. No past stream bits are reread.

This uses O(s log s+n) working bits. An elementary bound per repair is

\[
      2^{O(s\log s)}\,2^n\operatorname{poly}(s+n),
\]

which is generally far from polynomial in s. If no candidate exists,
exhausting the finite enumeration gives a sound rejection. This is not a
fast streaming algorithm, and it does not refute Target.

There is also a direct counting explanation. Let M be the number of valid
descriptions, so M <= 2^ell. At each fixed prefix length there are at most M
prefixes extendible by a circuit in the class: each must be the prefix of
one of those M tables. Every other prefix can enter the rejection sink.
A circuit description labels an extendible prefix. Thus a layered
transition system of width at most M+1 exists, independent of the time
needed to implement its transitions. Over all lengths the index costs
another O(n) bits. This is the elementary finite-language representation
principle, not a novel information-theoretic lower bound.

The arbitrary transition table can have exponentially many entries. Its
existence is not a polynomial-size uniform program with cheap transitions.
Conversely, a proof that ignores transition-computation time and excludes
even this small-space representation would be false. The ordinary
one-way-communication/state-counting attack was therefore stopped without
building another benchmark or formalizing an unrelated restricted bound.

Giving the machine a small-query oracle for Repair makes updates efficient
unconditionally in that oracle model. A purported lower-bound argument
that still holds with this oracle cannot establish Target. This concrete
model check is consistent with the locality discussion in [Locality, §1.3]
and [Modanese, §6]; it is not a blanket prohibition on circuit arguments.

## A further attempted shortcut and the remaining obligation

We also considered diagonalizing against an update algorithm and encoding
its simulation as a size-s circuit. If an update takes s^c steps, the
standard computation-to-circuit construction gives only a bound of about
s^c times logarithmic overhead. For arbitrary c>1 this does not guarantee
that the constructed table has a circuit within the **same** budget s.
Increasing the budget also changes the presumed algorithm's resource
bound. No self-consistent size-s construction was obtained. This rejects
that proposed derivation; the simulation upper bound is **not** a lower
bound on every possible encoding of the computation.

The unresolved step is computational: either establish Target with a
method sensitive to uniform transition time, or find a different proved
bridge and a lower bound that meets its hypotheses. Showing that one
candidate repair procedure is slow will not do; another streaming method
could maintain a different representation entirely. Merely verifying
that a supplied D agrees with C can require general circuit equivalence,
but naming this hard-looking subproblem is not an unconditional time lower
bound or evidence that every streaming solver must perform that operation.

No positive all-algorithm lower-bound argument survived this investigation.
The retained target is an open research obligation, **not an active proof
candidate**. There is no reason here to extend the phase-28 solver, enlarge
its benchmarks, or rerun its Lean checks. No new executable or Lean theorem
was added, and no new claim about test counts is made.

## Sources actually read

Retrieved 2026-11-06 UTC. The paper versions and the inspected parts are:

- **[MMW]** Dylan M. McKay, Cody D. Murray, R. Ryan Williams,
  *Weak Lower Bounds on Resource-Bounded Compression Imply Strong
  Separations of Complexity Classes*, STOC 2019, pp. 1215–1225,
  [DOI](https://doi.org/10.1145/3313276.3316396).
  [Author-hosted camera-ready PDF](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf):
  Theorems 1.2–1.4 (PDF pp. 2–3), streaming model (§2, p. 5),
  Stream-Merge and Algorithm 1 (§4, p. 8), Theorem 1.3 proof (§5, p. 9).
  SHA-256: `bc6d4178bac7aa09d5f531a4eae820b4adf20afb2fd58ea93ca9b37038b27f03`.
- **[Modanese]** Augusto Modanese, *Lower Bounds and Hardness Magnification
  for Sublinear-Time Shrinking Cellular Automata*,
  [arXiv:2007.12048v3](https://arxiv.org/pdf/2007.12048v3):
  Theorem 1 (p. 2), Definition 2 (p. 6), Merge and Theorem 14 (§5, pp. 16–17),
  limitations and locality (§6, pp. 18–19).
  SHA-256: `ae59a7ffa8c1f4b204a9f28c0bdf5b79c6670c3c0165f1de7b544461ee61b4a4`.
- **[Locality]** Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Jan Pich,
  Ninad Rajgopal, Rahul Santhanam, *Beyond Natural Proofs: Hardness
  Magnification and Locality*,
  [arXiv:1911.08297v1](https://arxiv.org/pdf/1911.08297v1):
  selected frontiers (§1.1, pp. 3–4), locality explanation (§1.3, pp. 8–9),
  selected prior magnification results (Appendix A, pp. 50–52).
  SHA-256: `e3851494208edda63dee2fb09083ef14972f22ddb761881fe507d1eaae36aa8b`.

Only the indicated statements and arguments are used. This is not a
reverification of all results in these papers, and none is attributed to
this project. Source PDFs are cached outside the repository; this note
records URLs and byte hashes rather than vendoring the publications.
