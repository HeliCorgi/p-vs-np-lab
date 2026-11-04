# What the implemented decision key forgets, and what forces it to remember

This experiment directly calls the [decision label](../src/pnp_lab/decision_labels.py)
on each residual and each same-scope anchored OR, then tests the
[pruning driver](../src/pnp_lab/decision_pruning.py) with one common width cap.
It does not infer key equality from agreement of SAT answers.

## A positive theorem with an unrestricted residual problem

Choose k tags t, primary bits y and private bits z. Add the width-three
CNF for each equality `t_i = y_i XOR z_i` (four forbidden patterns),
and a CNF K on y with proper width-two/three clauses and no units. A
general 3-CNF with three distinct variables per clause is allowed; the
clauses may couple all blocks. K is not assumed tractable or satisfiable.

At any depth d in which only tags have been assigned, the i-th tag
equation either keeps its four ternary clauses or becomes two binary
clauses for `y_i XOR z_i = constant`. These are complete parity
sign-orbits on their supports. A normalized K-clause cannot remove any
of them by subsumption, since each tag support contains only one y
coordinate. Nor can a tag clause subsume a K-clause. The tag scopes
use private z_i and so cannot join a sign-orbit from K. Each tag
equation has its own z_i, absent from all the remaining nonlinear
clauses, so every tag row can be satisfied for every choice of y and
the unassigned tags. Existential affine projection therefore removes
these rows. Projection of rows discovered *within* K is unaffected.

Consequently **all the affine labels on this depth equal the label of K
in the same named scope**, including the constant-label cases. Applying
this at successive depths, the driver keeps at most one raw branch
through every tag split. It need not find a model of K to do so. If it
must still solve K after those splits, no polynomial bound on that
remaining work has been established. A bare unit in K may subsume a
clause of a tag orbit, which is why the syntactic restriction on K is
stated. The claim is for the present extractor, not every logically
equivalent presentation.

## A redundant extension causes exponential retained width

For each core coordinate v in y,z add two fresh private bits a,b and
the marker `exactly_one(v,a,b)`, encoded by these four common clauses:

    v OR a OR b;  NOT v OR NOT a;  NOT v OR NOT b;  NOT a OR NOT b.

These additions impose **no constraint at all on the old coordinates
after the marker bits are existentially removed**. For v=1 take a=b=0;
for v=0 take a=1,b=0. They need not preserve the count of witnesses.

For a connected comparison take `k≥3` and use in BOTH arms the same K
of positive triples `y_i OR y_(i+1) OR y_(i+2)` with indices cyclic.
The all-one y word works, so for every t there is an actual SAT witness:
set `z_i = 1 XOR t_i` and extend the markers as above. Overlapping
triples connect all blocks in the incidence graph. The same negative
proof works with any satisfiable proper K as above (choose one model of
K), if connectivity is not required.

**Marker persistence in individual labels and anchored ORs.** All markers
are common to every tag-prefix residual. In the distributed OR of two
residuals, each common clause survives as its union with itself unless
subsumed. Every clause involving a private marker bit before distribution
was such a common marker clause. All its unions with other clauses are
subsumed by that common clause. No source nonmarker clause mentions a
private marker bit and each marker clause contains at most one y/z bit.
Before and after OR there are no nonmarker clauses of width less than
two at these depths. Thus none of these can subsume any marker. Distinct
marker clauses do not subsume one another. Every private-marker support has
only one sign pattern, on two or three bits, so the XOR extractor leaves
all these clauses in the nonlinear core. In particular **every y,z and
private marker bit remains visible**. Common clauses of K also deal with
extra OR products by subsumption; the argument does not require that all
nonmarker terms become affine.

Whenever the label has a nonlinear core, its pair (remaining CNF,
projected parity rows) represents exactly the projected model relation on
the named bits that occur in the core: row elimination quantifies only
bits outside this core. Equality of two such keys therefore also implies
equal projections onto any common subset of retained bits, in particular
onto y,z here. Distinct keys need not imply opposite decisions.

At depth d let E_a be the projected solution set on y,z of the marked
residual with tag prefix a (split the first d tags). Every point of E_a
has the specified d bits of `y XOR z`. The E_a are pairwise disjoint
and each is nonempty by the witness above. For fixed anchor b, the
OR with partner a projects on the same y,z bits to `E_b ∪ E_a`.
This gives distinct relations for all `2^d−1` partners. There are
therefore `2^d` distinct individual keys and, for EVERY anchor,
`2^d−1` distinct partner keys. All retain their nonlinear markers, so
none is a terminal YES. They are satisfiable, so none is a terminal NO.

By induction, if the driver processes all tag variables first, it
retains **exactly `2^d` live branches after tag depth d** until a cap
stops it. There is no deletion from the individual or anchored collision
rules and no terminal return at those layers. Ordered or unordered choices
of anchor within a layer do not change the argument. The supplied family
has 7k variables and O(k) clauses: even in literal-index encodings its
size is O(k log k). This is an all-k obstruction for a specified solver
and split order, not a lower bound on SAT or on adaptive choice of order.

This obstruction even has an explicit repair on the family: recognize the
disjoint private pairs a,b that only occur in their four marker clauses,
verify these occurrences, and existentially remove the four clauses and
their two private variables. The two extensions for v=0 need not be listed
to decide existence. This restores exactly the unmarked formula. Recognizing
such a pattern would not bound key diversity on unrelated 3-CNFs. The
present benchmark records the behavior *before* such a repair.

## Reproduction

The [experiment](../experiments/pruning_codec.py) calls the implemented
codec for both twins at every tag depth for k=1..4 (small k uses an empty
or binary core). Every marked anchor/partner pair is actually constructed,
canonicalized and labelled, sharing the result between the two orientations
of the same pair. The [record](../results/pruning_codec.json) separates
these observed counts from the proof for all sizes. On the coupled k=4
inputs, under the same cap 4, the unmarked affine driver returns SAT after
retaining just one branch at all four tag levels. The syntax-only driver on
that unmarked input and the affine driver on its marked twin both retain
widths 1,2,4,8 and return UNKNOWN. The marked twin remains SAT, as its
original-CNF witness independently confirms.
