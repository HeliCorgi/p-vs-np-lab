# A finite oracle for semantic support and simultaneous pooling

This audits a mechanism in the [support localization theorem](support_localization.md).
It does **not** computationally certify an asymptotic hard family. The
[oracle](../src/pnp_lab/support_localization.py) exhausts finite sets of raw
clauses and Boolean words. It is independent of the proof-size measure,
Hall matching, and integer-elimination implementation.

## A width-four closure on seven proper triples

Use one pivot and seven pairs of distinct private leaf variables. Each
clause contains the pivot and its own leaf pair; the pivot has one sign
in three clauses and the other in four. Consider each six-leaf scope
arising from a choice of three petals. Each scope contains **no original
clause**. For each raw subset of size $t\ge2$, the $2t$ private leaves
are exactly its unique neighbors, and its neighborhood has $2t+1$
variables. Use $\delta=2$, $s=6$ (strictly less than the seven raw
clauses), $w=4$, and $b=6$. These parameters meet both theorem windows.

The [experiment](../experiments/support_localization.py) runs on the
original and a signed permutation with reversed input order. Per input:

| Quantity checked | Count |
|---|---:|
| Complete raw clause subsets / Boolean assignments | 128 / 32,768 |
| Raw / derived lines in exhaustive proper, no-weakening width-four closure | 7 / 12 |
| Semantically minimum raw premises for each derived line | 2 |
| Six-leaf scopes checked | 35 |
| Scopes attaining $b/\delta=3$ for the pooled *minimum* supports | 30 |
| Scopes attaining 3 for structural $K(S)$ | 35 |
| Same-ambient unit edges / two-coordinate faces checked | 210 / 525 |

For example on leaves $2,3,4,5,8,9$ the clauses on leaves $2,3,8,9$
and $4,5,8,9$ have minimum supports $\{0,3\}$ and $\{1,3\}$
(zero-based raw IDs). Both follow from a pool of three raw clauses;
counting the two witnesses separately overcounts. The five all-same-sign
petal triples induce no learned lines on their six leaves, yet their
structural common support also has size three. A structural container
need not be a smallest semantic support.

**How checked.** Enumerate non-tautological binary resolvents with no
subsumption deletion and no weakening. For each line, inspect raw subsets
in increasing cardinality and retain every minimizer whose Boolean model
bitset contains no word falsifying the line. For each scope union these
minimizers, then separately compute $K(S)$ from *all* raw subsets of at
most $s$ clauses whose unique neighbors lie in $S$. Compare the pooled
models and learned truth tables. The mathematical theorem additionally
covers weakening; the finite enumeration is explicitly for this narrower
closure. Signed examples are SAT controls.

For a coordinate face, the four words must fix *all other coordinates*
to the same values, including coordinates outside the reported scope.
The oracle finds the common base by intersecting shifted model bitsets
of $K(S)$. The experiment directly evaluates all four words against
the raw clauses of $K(S)$ and the learned clauses; the same is done
with two words for singleton axes. Alternating the four quadratic
feature vectors isolates the indicated pair coordinate. These are
witnesses for individual faces; no single six-dimensional subcube or
global assignment satisfying an arbitrary full formula is asserted.

## Two ways scope intuition can go wrong

1. **Actual proof parents vs semantic premises.** Two disjoint paths
   prove the same non-axiom ternary target. The displayed width-three
   proof uses seven raw ancestors; the unique shortest semantic
   support consists of two *other* raw clauses. The path in the first
   proof can be made arbitrarily long. The experiment replays its
   pivots, and tests all 512 raw subsets of the nine-clause example.
2. **A two-bit constraint is not a proper three-variable axiom.**
   The binary clause $x\lor y$ admits both unit edges but forbids a
   corner of the full two-dimensional square; the quadratic polynomial
   $(1-x)(1-y)$ vanishes on all its models. The unit clause $x$ pins
   its coordinate. Both have positive unique-neighbor expansion on
   every nonempty subfamily. The proper-ternary hypothesis is needed
   to obtain a surplus of at least two from peeling.

## Check against the real 31-variable core and budget discipline

The [phase-16 finite core](correlation_proof_boundary.md) does **not**
satisfy positive unique-neighbor expansion all the way up to the large
family's threshold. In the 152-clause prefix, clauses 0, 138, 2, 59
use six variables, each exactly twice. Their boundary is empty. For any
$1\le t\le3$ clauses of this core, pairwise support intersections are
at most one; hence each selected clause has at least $4-t$ private
variables. Four is therefore the smallest number with empty boundary.
The explicit four-clause witness was located by a pair-symmetric-
difference index. This says **nothing** about whether the four clauses
are inconsistent, or about which sign pattern is hard; it checks an
incidence hypothesis only.

For $m$ clauses on $n'$ occurring or scoped variables, the raw semantic
table has $2^{m+n'}$ bits, besides indices, incidence sets, closure
and witness data. The oracle also charges candidate resolution pairs,
subset visits, bitset entailment tests, and face checks, separately from
the exponentially wide bit operations themselves. Labels are compressed.
Preflight and in-loop caps return `UNVERIFIED` with no partial theorem
data; none of this is a polynomial discovery procedure. See the
[reproducible report](../results/support_localization.json).
