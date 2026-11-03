# Certified parity cuts, and a barrier to CNF-only extraction

The previous [mixed solver](mixed_solver.md) parameterizes the XOR equations
and enumerates the distinct affine observations made by the CNF. This note
studies a polynomial preprocessing step: derive justified XOR equations from
recognizable exactly-one constraints in the CNF, add them to the existing XOR
system, and retain the original CNF.

The step can give a short contradiction where the previous algorithm visits
exponentially many representatives. It does **not** make the combined solver
polynomial-time on general inputs. Two all-size families establish its remaining
enumeration cost. More strongly, the CNF component of our existing 3SAT bridge
has full affine hull: even a complete extractor of unconditional parity
consequences from that CNF cannot add a nontrivial equation.

These are explicit mathematical arguments about the stated algorithms and
representations. They are not a P versus NP resolution, a lower bound for all
SAT algorithms, or a claim of novelty for cardinality detection, parity
reasoning, or their combination.

## 1. The inference rule, including signed literals

Let a normalized, non-tautological cover clause be

\[
 C=\ell_1\lor\cdots\lor\ell_s.
\]

For every pair `i < j`, require an explicitly present binary exclusion clause

\[
 E_{ij}=\neg\ell_i\lor\neg\ell_j.
\]

The cover requires at least one true literal. The exclusions prevent two true
literals. Every model therefore has exactly one true literal among the
normalized occurrences, and hence satisfies

\[
 \ell_1\oplus\cdots\oplus\ell_s=1.                 \tag{1}
\]

Write a signed literal as `ell_i(x) = x_{v_i} XOR epsilon_i`, where
`epsilon_i=1` denotes negation. The equation added to the unsigned-variable
XOR system is

\[
 \bigoplus_{i=1}^s x_{v_i}
   =1\oplus\bigoplus_{i=1}^s\epsilon_i.           \tag{2}
\]

For example, exactly one of `x, not y, z` yields `x XOR y XOR z = 0`, not 1.
The sign adjustment is necessary even when a cover contains only negative
literals.

### Normalization and degenerate cases

The recognizer removes repeated literals before treating a clause as a cover.
Without this, a clause such as `(x OR x)` would count a true literal twice and
produce the wrong parity. A clause containing both `x` and `not x` is
tautological and is not used as a cover. Thus a nonempty accepted cover has
distinct underlying variables.

Every exclusion must normalize to **exactly** the required two literals. A
clause with an extra disjunct does not establish the exclusion. Repeated
literals in a raw exclusion clause are harmless after normalization, and the
certificate still refers to its original raw clause index.

An empty cover is a false input clause. Its consequence is `0=1`, with no
exclusions needed. A unit cover yields the corresponding one-variable XOR
equation, also without exclusions. These are sound boundary cases of the same
inference; no implicit SAT search is hidden in them.

## 2. Strengthening preserves every model

Let `A` be the input XOR system, `F` the original CNF, and `D` the conjunction
of any equations justified by the rule. The inference proves `F => D`.
Consequently, for every assignment `x`,

\[
 (A(x)\land F(x))
 \quad\Longleftrightarrow\quad
 (A(x)\land D(x)\land F(x)).                       \tag{3}
\]

The strengthened problem has the same full assignments, not merely the same
SAT/UNSAT answer. Witnesses and exact model counts therefore retain their
meaning. The remaining CNF must be retained: odd parity alone permits three,
five, or more true literals and is not equivalent to exactly-one.

If the strengthened XOR system is inconsistent, (3) proves UNSAT without any
quotient enumeration. Otherwise, the existing exact mixed solver runs on the
strengthened system and the unchanged CNF. Its earlier correctness argument
continues to apply. A budget limits representative visits; the polynomial
preprocessor may establish UNSAT even with `max_cells=0`.

This implementation performs one pass over covers in the original CNF. It
does not search for arbitrary cliques, generate new CNF clauses, perform
resolution or probing, repeatedly discover cuts after simplification, or use
a general unit-propagation engine. Unit covers are handled by the inference
above.

### What happens to the rank parameters

For a consistent input XOR system, let `d` be its affine dimension and let `r`
be the rank of the variables observed by the normalized CNF, as defined in
[the mixed-solver note](mixed_solver.md). Assume that adding the cuts is also
consistent and adds `h` independent equations. Then

\[
 d'=d-h,\qquad r'=r-h,\qquad d'-r'=d-r.             \tag{4}
\]

To see this, let `S` be the set of observed variable coordinates. All added
equations involve only `S`. Directions in the original XOR solution space
that are zero on `S` satisfy every homogeneous cut automatically. Thus the
kernel of the projection to `S` has the same dimension before and after
strengthening, while the total affine dimension drops by `h`. Rank-nullity
gives (4).

In particular, adding these cuts cannot increase the number `2^r` of quotient
cells. It can still add preprocessing work, and it need not reduce `r` at all.
This is not a claim that every run becomes faster in wall-clock time.

## 3. Certificates and an independent checker

The implementation is [parity_cuts.py](../src/pnp_lab/parity_cuts.py).

| API | Meaning |
|---|---|
| `derive_parity_cuts` | Find the supported covers and return a JSON-compatible derivation certificate, including a row-combination contradiction when found. |
| `check_parity_cut_certificate` | Independently verify all referenced clauses, signed equations, and any supplied contradictory combination. A valid certificate without a contradiction establishes sound strengthening only. |
| `solve_with_parity_cuts` | Add the justified equations and run the exact quotient solver if needed; its exploration flags have the same meanings as in `solve_mixed`. |
| `check_parity_cut_unsat_certificate` | Verify the UNSAT envelope, including a contradictory cut proof or an explicitly supplied residual quotient certificate. |

The preprocessing certificate has kind `exactly-one-parity-cuts-v1` and
contains the variable and input counts. Each cut records:

- `cover_clause`: an index in the **original raw CNF**;
- `exclusion_clauses`: original clause indices in the recognizer's canonical
  sorted-cover pair order;
- `equation`: the unsigned variable mask and right-hand-side bit.

Original input XOR rows are the already normalized
`AffineRelation.equations`, in their given order. They are followed by the
derived cut rows. A contradiction records indices of rows whose XOR equals
`[0, 1]`. A selector is a set of selected row positions, not a numerical sum
of coefficients over the integers.

The checker evaluates the referenced clause supports and signs itself. For a
contradiction, it XORs the cited masks and right-hand sides directly; it need
not rerun the recognizer or Gaussian elimination. If all selected equations
hold on a putative model, their XOR must hold as well, so a verified `0=1`
excludes every model.

The recognizer need not find every valid cut for a supplied certificate to be
sound. Conversely, merely checking a collection of valid cuts does not prove
UNSAT. That conclusion requires a verified contradiction or a complete checked
residual search certificate. An incomplete search remains `UNKNOWN`.

The normalized input rows are a trust boundary inherited from
`AffineRelation`: this certificate does not separately reconstruct a proof of
their normalization from pre-normalization named rows. Experiments retain raw
inputs for independent semantic comparisons. The Python runtime, input
validation, integer operations, and checker code are also part of the trusted
implementation.

## 4. Polynomial cost of this preprocessing step

Let `L` be the number of literal occurrences in the raw CNF, let `m` be
its number of raw clauses, and let `n` be the explicitly listed variable count.
The full encoded bit length is `N`; variable identifiers, signs, and XOR rows
are included.

There are at most `m` candidate covers: the recognizer uses input clauses, not
all subsets of literals or all graph cliques. A cover of size `s` needs
`binom(s,2)` exclusion lookups. Across the input,

\[
 \sum_C |C|^2\le L^2.
\]

Building the normalized binary-clause index and checking these pairs is
polynomial in `N`. Even charging a linear scan of all input clauses for a
lookup, rather than assuming constant-time hashing, gives a polynomial upper
bound. Masks contain at most `n` bits; their arithmetic is charged by bit
length.

At most `m` cut equations are produced. Their clause-reference certificates
have polynomial size, bounded conservatively by
`O((m + L^2) log(m+2) + mn)` bits in addition to input bookkeeping. Using raw
clause counts here also charges the indices of premises that appear late in
an input with many duplicate clauses. Gaussian
elimination of the input rows plus these cuts can carry a provenance bit
vector for each row. XORing row masks and provenance vectors takes polynomial
bit time and space, and a final contradictory row uses only a polynomial
number of source-row indices.

Thus the preprocessor and its explicit contradiction certificate are
polynomially bounded. The combined solver still has the upper bound

\[
 \operatorname{poly}(N)+2^{r'}\operatorname{poly}(N)
\]

when a consistent strengthened system reaches the fallback enumerator. The
residual full-search certificate can still be exponentially large. A short
certificate on a recognized family does not provide short certificates or
efficient proof search for all UNSAT inputs.

## 5. Families the new rule resolves without enumeration

The previous counterfamily was the direct pairwise CNF for exactly one of
`k` variables, together with even parity. The cover and all exclusions are
present, so one cut supplies odd parity and immediately contradicts the input
XOR. This argument works for every size, not only tested examples.

A second useful family is the odd cycle. For odd `k >= 3`, with indices taken
modulo `k`, use the clauses

\[
 (x_i\lor x_{i+1})\land(\neg x_i\lor\neg x_{i+1})
 \qquad (i=0,\ldots,k-1).
\]

For each edge the rule derives `x_i XOR x_{i+1}=1`. XORing the `k` edge
equations cancels every variable twice and leaves `0=1`. This supplies a
polynomial-size contradiction assembled from several independently justified
cuts. No single edge is itself inconsistent.

These families verify that the preprocessor performs actual cross-constraint
reasoning. They do not establish a general polynomial bound.

## 6. The exact-two family still forces exponential enumeration

For `k >= 4`, define a CNF that requires exactly two true variables:

\[
 E^{(2)}_k=
 \left[\bigwedge_{i=1}^{k}\left(\bigvee_{j\ne i}x_j\right)\right]
 \land
 \left[\bigwedge_{i<j<\ell}
       (\neg x_i\lor\neg x_j\lor\neg x_\ell)\right].       \tag{5}
\]

The first group excludes zero true variables and excludes any assignment
whose only true variable is `x_i`. It therefore requires at least two true
variables. The second group forbids any three true variables and therefore
requires at most two. Conversely, every assignment of weight two satisfies
all clauses. There are `binom(k,2)` CNF models.

Add the independently satisfiable XOR equation

\[
 x_1\oplus\cdots\oplus x_k=1.                         \tag{6}
\]

Equations (5) and (6) together are UNSAT because weight two has even parity.
Every CNF clause has width at least three. There are no unit clauses, no
binary exclusions, and hence no cuts from this recognizer. Ordinary CNF unit
propagation would also have no initial step. The XOR equation has no forced
individual variable.

The input XOR has rank one, every variable occurs in the CNF, and therefore
`d=r=k-1`. The unchanged fallback must reject every one of its `2^(k-1)`
representatives, even in decision mode that stops on the first SAT witness.

There are `k + binom(k,3)` clauses and
`k(k-1) + 3 binom(k,3)` literal occurrences. Under a usual explicit encoding,
`N = Theta(k^3 log k)`. For every fixed `c`,

\[
 \frac{2^{k-1}}{(k^3\log k)^c}\longrightarrow\infty.
\]

This proves a superpolynomial worst case for the combined algorithm. It is a
family that is easy for a solver recognizing this cardinality representation,
not a lower bound for other methods.
The family shows precisely which stronger cardinality information this
particular rule does not recover.

## 7. A connected encoding barrier from the existing 3SAT bridge

Apply [the repository's reduction](two_cnf_xor_reduction.md) to the odd-cycle
CNF from Section 5. Each of its `2k` binary source clauses is padded to three
occurrences by repeating its last literal. The reduction introduces three
fresh helpers per source clause, places them in one even-parity equation,
and pairs each helper positively with one padded original literal in a
binary clause.

The target has:

| Quantity | Value |
|---|---:|
| Original variables | `k` |
| Fresh helpers | `6k` |
| Total variables | `7k` |
| Binary CNF clauses | `6k` |
| Mutually disjoint ternary XOR rows | `2k` |
| XOR rank | `2k` |
| Affine dimension and observed rank | `d=r=5k` |

Each target binary clause contains a fresh positive helper. No helper occurs
negatively in the target CNF. Its complementary binary exclusion therefore
does not occur, so no target clause supplies an exactly-one cut. There are no
unit clauses. Every target variable is observed, which gives `r=d`.

The reduction preserves UNSAT, so the fallback visits exactly `2^(5k)` cells
on every odd `k >= 3`. For `k=3` that is 32,768 cells on 21 target variables;
for `k=5` it is 33,554,432 cells on 35 variables. A budgeted run on the latter
does not establish UNSAT by enumeration; the all-size statement follows from
the reduction and the enumerator's control flow.

The constraint graph remains connected. Each helper triple connects the two
original endpoints of its source edge, and the original edges form a cycle.
Every helper occurs in both a CNF clause and an XOR row. Thus the observed
dimension is not inflated by unconstrained or disconnected padding.

With sparse named clauses and XOR triples, the input encoding has
`N = Theta(k log k)`. The implementation's materialized dense row masks may
occupy `O(k^2)` bits; charging those masks as part of an explicit alternative
input representation still yields polynomial input size and a
superpolynomial enumeration bound.

The directly encoded odd cycle is solved by cuts and Gaussian elimination,
while its satisfiability-preserving bridge image defeats this recognizer.
Correct reductions preserve answers, not the effectiveness of a particular
inference procedure.

## 8. Stronger theorem: the bridge CNF has full affine hull

The previous failure is not only about a missing syntactic pattern. Consider
any output of the existing bridge whose source has no empty clause. Its CNF
component has the form

\[
 F(o,h)=\bigwedge_{j=1}^{H}\bigl(\ell_j(o)\lor h_j\bigr),  \tag{7}
\]

where `o` is the original variable tuple, each `ell_j` is a signed original
literal, and each `h_j` is a distinct positive helper appearing in exactly
one CNF clause. Repeated original literals and unused original variables are
allowed. The XOR constraints are deliberately **not** premises in this
theorem.

**Theorem.** The set of models of (7) has affine hull equal to the entire
Boolean vector space on all original and helper variables. Equivalently,
every affine XOR equation entailed by this CNF alone is a tautology after
normalization.

**Proof by coordinate differences.** Setting every helper to 1 satisfies
every clause for any original assignment. For any original coordinate `i`,
two such models can differ only at `o_i`; their XOR difference is the
coordinate unit vector `e_i`.

For a helper coordinate `h_j`, choose an original assignment making
`ell_j(o)` true. Such an assignment exists because `ell_j` is an individual
signed literal. Set all helpers to 1. Both that assignment and the assignment
with only `h_j` flipped to 0 satisfy the CNF: clause `j` has its original
literal true, and every other clause still has its helper true. Their
difference is `e_{h_j}`.

Differences of CNF models therefore include every coordinate unit vector and
span the whole space. If an affine equation `a dot x = b` holds on all CNF
models, subtracting each exhibited model pair gives `a_i=0` for every
coordinate. The CNF has a model, so the equation with all zero coefficients
also forces `b=0`. This proves the claim. The empty source formula is harmless;
a source empty clause is excluded because its target CNF is already false.

The proof is constructive and has a polynomial-size witness. For each target
coordinate, supply the two CNF models above; a checker verifies both models
against the raw CNF and verifies that their XOR is the corresponding unit
vector. There are `n_target` pairs of `n_target`-bit assignments. No
exponential truth table or assumption that an experimentally computed hull
generalizes is needed.

[`src/pnp_lab/affine_hull.py`](../src/pnp_lab/affine_hull.py) implements this
specific construction as `coordinate_separation_certificate_for_leaf_cnf`.
The independently evaluated checker `check_cnf_coordinate_separation` verifies
every raw-CNF model pair and coordinate difference. A certificate of kind
`cnf-coordinate-separation-v1` contains `n_variables`, a verified
`base_model`, and one pair `{coordinate, left, right}` for every coordinate.
The base model also handles the zero-variable case: an empty list of pairs
alone would not distinguish true from false CNF. The witness has
`O(n_target^2 + 1)` bits, and direct clause evaluation has polynomial bit cost.
This is a witness of full affine hull on supported inputs, not an algorithm
for computing the affine hull of an arbitrary CNF.

The polynomial-input-size claim uses an explicitly represented variable
scope, as in the bridge's explicit variable list; all target variables also
appear in the odd-cycle family. The constructor's
more general API accepts an integer `n_variables` and permits unused
variables. If a caller declares an enormous scope using only a binary count,
an `O(n_variables^2)` witness need not be polynomial in that count's encoding
length. No such succinct-scope claim is made here.

### Consequence for the research direction

Even a semantically complete extractor of all unconditional CNF-to-XOR
consequences cannot strengthen the bridge image: there are no nontrivial
equations to find. Combining the resulting tautologies with the existing
consistent XOR rows cannot yield a contradiction. The odd-cycle bridge family
therefore exposes a limitation of this entire restricted strategy, beyond
the particular exactly-one recognizer.

This does **not** block reasoning whose premises include both the CNF and the
existing XOR rows. Joint consequences can be informative; the combined
odd-cycle instance is UNSAT. Other possible changes include learning
non-affine constraints, changing the representation, or recognizing and
undoing an encoding. Their soundness, discovery cost, and worst-case total
cost would be new obligations. The full-affine-hull theorem supplies no lower
bound for those methods and no P versus NP separation.

## 9. Formal scope and reproducibility

[`Formal/ExactlyOneParity.lean`](../Formal/ExactlyOneParity.lean) states the
exactly-one-to-parity inference for arbitrary-length lists of evaluated
Boolean literals, proves the signed-literal translation, and proves that
adding justified equations while retaining the original predicate preserves
models and satisfiability. The proofs use induction and finite Boolean case
splits, not a bounded-size enumeration standing in for a general theorem.

[`Formal/BridgeAffineBarrier.lean`](../Formal/BridgeAffineBarrier.lean)
formalizes the bridge model pairs and the finite affine-equation consequence:
if a normalized finite XOR row holds on every model of the bridge CNF, its
support is empty and its right-hand side is false. This is the precise
no-nontrivial-equation statement behind the finite-dimensional full-hull
description above. The CNF and the existing XOR rows remain distinct premises
in this claim. The main theorem is
`BoundaryLab.BridgeAffineBarrier.bridge_has_no_nontrivial_affine_equation`;
its general coordinate-separation lemma includes an explicit nonempty-model
premise, including when the coordinate type is empty.

The Python recognizer, raw-clause indexing, certificate parser, Gaussian
normalization, and bit-cost bounds remain separate implementation and
mathematical obligations. An audited Lean inference theorem is not an
end-to-end formal verification of the Python solver or a complexity proof.

Use the repository's reproduction command to run the executable checks and
compare committed deterministic reports:

```bash
python scripts/reproduce.py --out-dir reproduced --check
```

Lean is checked separately:

```bash
lake build Formal
python scripts/audit_axioms.py
```

## Prior work and attribution

Armin Biere, Daniel Le Berre, Emmanuel Lonca, and Norbert Manthey,
[*Detecting Cardinality Constraints in CNF*](https://fmv.jku.at/papers/BiereLeBerreLoncaManthey-SAT14.pdf),
SAT 2014, studies syntactic detection using binary/ternary clauses and a more
general propagation-based approach. It describes the pairwise encoding of
at-most-one and binomial cardinality encodings used as background here. Our
small recognizer is a deliberately narrower, certificate-producing rule.
There is no novelty claim or benchmark comparison with the methods in that
paper or with modern SAT solvers.

The previous notes give the background and proof obligations for
[general mixed solving](mixed_solver.md), the
[3SAT coverage bridge](two_cnf_xor_reduction.md), and
[what would constitute a P versus NP solution](solution_criteria.md).
