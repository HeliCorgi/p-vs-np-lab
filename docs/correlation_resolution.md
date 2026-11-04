# Nonlinear correlations: an exact width-four refutation of the previous blind input

[Implementation](../src/pnp_lab/resolution_closure.py) · [tests](../tests/test_resolution_closure.py) · [experiment](../experiments/correlation_resolution.py) · [results](../results/correlation_resolution.json).

The previous [integer experiment](global_integer_theory.md) retained no local
affine equation on the signed 31-variable, 152-clause projective-line fixture.
Every singleton integer probe was also inconclusive. This phase retains
**forbidden combinations of actual Boolean values**, represented as clauses,
and derives new ones by ordinary resolution. The same raw input has a checked
width-four refutation. Width three is provably insufficient for that input.

This is a finite proof-discovery result in an established proof system, not a
new general SAT algorithm or a claim of mathematical novelty. The result is
useful precisely because its information content, proof rule, discovery cost,
and limitation can be stated independently.

## 1. What is retained that the integer projection erased?

The rule is

\[
 \frac{A\lor x\qquad B\lor\neg x}{A\lor B}.
\]

Here A and B are disjunctions not containing the pivot variable. For these two
relations, joining their satisfying tables and existentially projecting away
x gives **exactly** the relation A OR B. Adding that consequence to the whole
formula is sound. It is not necessary to replace the rest of the formula or to
forget its other occurrences of x.

In the retained proof, an early derived binary clause is

\[
                 x_{23}\lor\neg x_{30}.
\]

It excludes one of the four pairs of values, namely x23=0, x30=1, while keeping
the other three. Those three points have full integer affine lattice in two
coordinates. Projecting this learned relation back to affine equalities and
congruences would therefore erase it again. The clause representation retains
the forbidden pair and can combine it with further derived clauses.

This binary clause's proof uses 13 original clauses and 27 proof nodes. The
first retained unit, NOT x24, uses 41 original clauses and 98 nodes. These are
statistics of the first such lines **in the pruned final proof**, not a claim
that no earlier line in the discarded search history had the same width.
They also show why a small conclusion need not be a consequence of one small
raw fragment. The final contradiction uses 115 original clauses.

## 2. Discovery and independent proof replay

The finder takes only the original CNF. It canonicalizes each clause, discards
tautologies, and queues stored clauses by increasing width. A candidate pair
is obtained from opposite signed occurrences of a pivot. A non-tautological
resolvent is retained if it fits the requested width and is not subsumed by an
already known clause. New stronger clauses retire active supersets.

Retiring an active row does not delete its proof history. Clauses are still
available as parents of earlier discoveries. This distinction is necessary:
counting only active rows would understate the memory and proof-discovery cost.

When an empty clause is found, keep just its ancestor DAG. Its format is:

* An input node names an original zero-based clause index.
* A resolution node names two earlier nodes and a signed pivot, which must
  occur in the left parent and with opposite sign in the right parent.
* The last node must reconstruct the empty clause.

The certificate includes a width bound but does not supply alleged derived
clauses. The independent checker reconstructs each exact resolvent using sets
of signed literals, checks its width, rejects tautologies, and checks the
empty final line. It does not use the finder's bit masks, priority queue,
candidate-pair index, subsumption state, generator metadata, or saved proof.

Variable names in the search masks are compressed to the variables actually
occurring in the input. Merely declaring a large unused variable range must
not allocate masks of that declared length. Original names and clause indices
remain in every certificate.

## 3. An independently checked lower bound at width three

An UNKNOWN result after a budget is exhausted is not a lower bound. To
distinguish that outcome, completed saturation also emits a different kind of
certificate: a collection C of nonempty clauses of width at most w.

The separate closure checker verifies:

1. Every usable original axiom has a subclause in C.
2. Every non-tautological resolvent of two clauses of C, when its width is at
   most w, also has a subclause in C.
3. The empty clause is not in C.

These facts exclude an ordinary resolution refutation of width at most w.
Induct along any proposed derivation, maintaining a clause of C contained in
each proof line. For a resolution step, if one maintained clause omits the
pivot, it already lies inside the target. Otherwise the maintained clauses
resolve to a subclause of the target and condition 2 applies. A weakening
preserves the same containment. An empty target would require an empty member
of C, contradicting condition 3. The checker does not need to assume that C
is satisfiable or to solve SAT on C.

For the 31-variable fixture, the 152 original clauses themselves form such a
width-three closure. Any two distinct raw clauses have unsigned triple
supports intersecting in at most one variable; in particular, there is at
most one clause per unsigned triple, including clauses with different signs.
If two raw clauses resolve non-tautologically, their resolvent
has width four. Hence width-three saturation cannot add its first new clause.

Width-four discovery does refute the input. These two independently checked
certificates establish its **exact minimum ordinary-resolution width of four**,
also allowing weakening. Extension axioms and other proof systems are not part
of that assertion. A closure certificate establishes absence of a bounded-width
proof; it is never a certificate of satisfiability.

## 4. Finite results and costs

The original negative fixture gives the following deterministic counts:

| Quantity | Value |
| --- | ---: |
| Original variables / clauses | 31 / 152 |
| Width-three stored rows at completed closure | 152 |
| Width-four stored rows over the whole search | 26,826 |
| Candidate-pair visits | 180,420 |
| Subset lookups for subsumption | 463,497 |
| Peak active rows | 9,840 |
| Literal slots over all stored rows | 102,696 |
| Retained proof nodes | 368 |
| Retained original / resolution nodes | 115 / 253 |
| Retained proof width | 4 |
| Largest parent-variable union | 5 |
| Retained proof depth | 22 |
| Compact JSON certificate bytes | 15,952 |

The pair count includes visits in both directions when both parents survive
until their queue turns. Superset checks, retired rows, duplicates, and the
peak agenda are also recorded in the report. The small retained proof is the
output of a substantially larger discovery search; its size alone does not
measure the algorithm's work.

Every successful proof step concerns at most five Boolean variables, since the
pivot adds at most one variable to a non-tautological resolvent of width four.
That is the width of the two-parent join before projection. It is distinct
from the number of variables in the whole input and from the number of raw
ancestors supporting a derived row. The [proof-system comparison](correlation_proof_boundary.md)
describes the relation to exact local-table operations and polynomial-calculus
degree.

Three additional signed variable permutations with clause and literal shuffles
also refute under the same default search caps. Their pruned proofs contain
449, 434, and 457 nodes. The finder gets no permutation key or geometric
description. The corresponding all-positive support patterns have checked
Boolean models; their shuffled versions also have checked models. Both widths
three and four reach a completed non-refuting closure on those four positive
controls, and the public refuter reports UNKNOWN.

### The earlier decision tree is only a baseline

The previous report already contained a 957-node raw decision-tree
refutation. Its leaves are original falsified clauses. For comparison, the
experiment converts that supplied tree to a resolution DAG, discards a
branch if its inferred clause omits the branch pivot, reuses identical
clauses, and trims the empty clause's ancestors.

That converted proof has 472 nodes: 126 original and 346 derived, at width
nine. The conversion is independently replayed and the source tree's hash is
recorded. The new width-four finder does **not** read that tree, its leaves,
its branch order, or the converted proof. This prevents a supplied proof from
being mistaken for autonomous proof discovery.

## 5. Resource limits and the asymptotic boundary

The API is

    resolution_refute(n, clauses, width=4,
                      max_rows=50000, max_pairs=1000000, max_subsets=5000000)

Each cap can be set to None. Row count includes historical inactive rows and
input nodes, not just the active frontier. The pair cap counts candidate visits;
the subset cap counts subset lookups in the subsumption search. These are
specific work controls, not claims of a wall-clock bound. A cap produces
UNKNOWN with no closure certificate and no assertion that all proofs of the
chosen width have been searched.

Independent replay also accepts optional node, actual line-width, and total
literal-occurrence caps. It raises the separate `ResolutionReplayLimit` when
one is exceeded, so callers can distinguish a budget-limited translation from
a malformed source proof. The declared width in a certificate is not used to
allocate storage: a loose header does not override the actual-row limits.

Without caps, at fixed width w, there are at most

\[
       C_w(n)=\sum_{j=0}^{\min(w,n)}2^j {n\choose j}
\]

distinct non-tautological clauses over n active variables. Each is inserted at
most once. There are at most a quadratic number of candidate-pair visits in
this universe; subset lookup contributes a factor at most 2^w. The mask
operations, incidence indexes, parent identifiers, and replay must also be
charged in bits. This gives a polynomial bound for **each fixed w**, with a
degree depending on w. It is a complete bounded-width proof search, not a
complete fixed-polynomial SAT algorithm.

The implementation preserves all inserted masks and parent records. Their
storage includes n-bit masks and identifiers of size logarithmic in the
number of stored rows, together with the occurrence indexes and agenda.
When w is allowed to grow with n, the clause universe can be exponential.
The caps do not turn an incomplete result into a negative answer.

Most importantly, [the existing resolution barriers](robust_ceiling.md)
already give other width-three CNF families requiring unbounded, indeed linear,
resolution width and exponential resolution length. Therefore finding width
four on this 31-variable fixture does not justify promoting fixed-width
resolution to a universal strategy. The [current proof-system review](correlation_proof_boundary.md)
states which exact encodings and inference rules those lower bounds cover.

## 6. Validation scope

Seven new tests cover the exact finite width comparison, signed scrambling and
proof tampering, caps, closure-certificate omissions, raw-index preservation,
and sparse variable names. They also check all 512 formulas formed from the
nine proper clauses on two variables at widths zero, one, and two against an
independent unsimplified closure procedure; at width two the result is checked
against all four Boolean assignments.

The proofs and closure certificates are finite independently replayable
objects. Formal semantic rules for related representations do not, by
themselves, constitute formal verification of the complete Python search,
its memory accounting, or a general P versus NP theorem.

