# Testing labels for decision-only pruning

In a pruning step one asks how many different labels the ORs of a fixed
residual (the *anchor*) with its partners can produce. If equal labels imply
equal satisfiability of these disjunctions, a collision permits removal of one
partner. If the anchor is satisfiable, every such OR is satisfiable. A known
polynomial upper bound on the number of different positive labels in these
batches would therefore also permit a deletion when the labels are distinct.
The classic global sparse-target version is due to
[Mahaney](https://doi.org/10.1016/0022-0000(82)90002-2); see
[Grochow's account of the pruning proof](https://eccc.weizmann.ac.il/report/2016/162/).

Our goal here is narrower: use a *single small input at each size* to falsify
a proposed width bound, and use two opposite decisions to falsify a proposed
collision rule. The [actual CNFs](../src/pnp_lab/residual_controls.py) and
[finite controls](../results/decision_pruning.json) use labelled variables.
An OR is a union of two model sets on the **same** coordinates: a fresh
branch flag with multiple possible extensions must not secretly change the
model count. A circuit for the disjunction may use functionally determined
gate outputs without affecting counts.

## A comparator defeats all labels that retain the exact count

Make a width-three CNF on `3k` bits `(t,u,q)` with `k` bits per group.
Using the least significant bit first inside each word, start with the
constant `q[-1] = 1` and enforce

    q[i] = majority(t[i], not u[i], q[i-1])     (0 <= i < k)
    q[k-1] = 1.

For Boolean inputs A,B,C and output Q, use `¬A ∨ ¬B ∨ Q` and
`A ∨ B ∨ ¬Q` for each of the three input pairs (replace A,B by the
selected pair). This is majority equivalence. At the first bit the gate
reduces to OR and takes three clauses. Including the final unit clause gives
exactly `6k−2` clauses of width at most three. When the current input bits
differ the new high bit decides the comparison; when equal it passes through
the lower comparison. Thus q is unique for each t,u, and the original
formula holds iff `u≤t`. Literal-index bit encodings have length
`O(k log(k+1))`.

Split the most significant bits of t first. At depth d let `a` be the
fixed d-bit prefix, `r=k−d` and `W=2^r`. A residual `H_a` has the
`r` free t bits and *all* u and q bits as its common domain. Its exact
model count is

    S_a = sum_{v=0}^{W−1} (aW+v+1) = a W² + W(W+1)/2.

Moreover **every labelled model of H_0 is also a model of H_a**. Indeed
the top d bits of u were zero; all their carry states were one (comparison
on the low r bits already succeeded). With those u bits zero, an incoming
one remains one for either replacement t bit. When r=0 the incoming carry
is the fixed seed one; at d=0 containment is tautological.

Consequently the `2^d−1` ORs `H_0 ∨ H_a` for nonzero prefixes a have
pairwise different counts `S_a`, while they are all satisfiable and their
common anchor is satisfiable. This occurs **on a single layer of one input**,
not by mixing unrelated inputs or lengths. At d=k it gives `2^k−1`
positive labels for every label function whose value determines the exact
count. Bijections, in particular coordinate order changes within an individual
residual or renamings of an entire OR, preserve counts. The example is for
the stated split order and common-scope semantics; it does not force every
adaptive solver to explore this layer. If a label uses one parsimonious
encoding of the disjunction, the same counts still apply.

This rules out a *polynomial positive-label diversity argument* for
count-refining labels over all such batches. It does **not** rule out a
polynomial-time counting algorithm, a non-parsimonious reduction, a
different split order, or a decision label that forgets counts. If exact
counts were already polynomial-time computable on all 3-CNF, testing
nonzero would of course decide SAT directly.

## Fixed residues forget too much

For every integer modulus m≥1 take `k=max(1,ceil(log2(m)))` and fix
t=m−1. The residual A now has precisely m models by the same unique-gate
argument, on its 2k labelled coordinates. Let anchor H and alternative
B both be any contradiction on those coordinates, e.g. `x ∧ ¬x`. The
ORs `H ∨ A` and `H ∨ B` have exactly m and zero models. They have
the same count modulo m but opposite decisions. Modulus one is the
constant label and satisfies the same counterexample. The source chosen
for the counterexample may depend on the proposed fixed modulus.

The three functions need not be presented as unrelated branches: attach
two selector bits b,c to A, impose the units b=1,c=0, and split b,c first.
Prefix (0,0) is an inconsistent anchor, (1,0) is the positive partner,
and (0,1) is an inconsistent partner. This is an obstruction to the
residue as a *standalone universal collision rule*. An algorithm with
unit propagation would settle this example immediately. A tuple of fixed
positive moduli suffers the same issue by taking m to be their lcm.
The construction says nothing about sketches that include other information
or about arbitrary formula-dependent moduli.

## Why even an exact cover by projected 2-CNFs is demanding

For k disjoint clauses on positive triples, `F = AND_i (x_i OR y_i OR z_i)`,
there are `3^k` minimal satisfying words: precisely one bit is one in each
triple. Suppose a union of relations represented by *existentially projected
2-CNFs* equals the entire model relation of F. Auxiliary variables per
component are unlimited; cross-block clauses are allowed. Each component
must be contained in the solution set. Every 2-CNF is closed under
coordinatewise majority of three models: if the majority falsified both
literals of a binary clause, two of the three inputs would falsify each
literal, and those two pairs have a common input. Units work the same
way. Projection preserves this property by taking the majority of witnesses.
For context see [Schaefer, STOC 1978](https://doi.org/10.1145/800133.804350);
the elementary argument here suffices.

Project a component once more to any one triple. It cannot contain all
three unit vectors: their majority is zero, which that block forbids.
Hence this component covers at most `2^k` minimal words, regardless of
cross-block dependencies. Every such exact cover has at least
`ceil((3/2)^k)` components. This statement concerns a union of projected
2-CNFs on the retained source variables; it does not cover general
affine/majority-changing interpretations.

Even the exponential base is sharp up to a linear factor. For each triple
choose an omitted coordinate uniformly and use the clause on the remaining
two. The conjunction of these k binary clauses lies inside F and covers any
fixed minimal word with probability `(2/3)^k`. With
`L=ceil((k ln(3)+1)(3/2)^k)` independent components, the expected number
of uncovered minimal words is at most `3^k exp(−L(2/3)^k)<1`. Some choice
covers every minimal word; by monotonicity it then covers every model of F.
This is an existence argument for a cover, not a polynomial-time method for
listing it. F is trivially satisfiable. Nothing about this example rules out
polynomial decision via one selected witness or an existential-preserving
compression that changes the set of models.

## What was checked

The [experiment](../experiments/decision_pruning.py) exhausts actual CNF
assignments including gate bits for k=1..4 and compares every residual's
entire set with the corresponding restriction of the original. It directly
counts anchored unions and checks the collision on eleven moduli. It also
checks every subset of the seven nonzero triples for the one-block majority
bound. For k=8,32,128,512 it builds only the original CNF; the large label
counts are formula predictions, not measured search runs. None of these
examples yields a sound sparse decision key for unrestricted 3-SAT.
