# One repair that works, and one that still fails exponentially

The [decision driver](../src/pnp_lab/decision_pruning.py) keeps a disjunction
of actual raw restrictions. A key is only used to compare SAT status or
settle a case; the algorithm never branches on the key. The
[`blocked` policy](../src/pnp_lab/decision_labels.py) first eliminates
blocked clauses to a fixed point, then applies the same affine label as
before. All case counts below are for **deciding** SAT, not modeling the
sets of satisfying assignments exactly.

## Why the new preprocessing is sound

A clause C is blocked on literal l if, for every other clause D containing
the opposite literal, resolving C and D on l produces a tautology (with
some other variable occurring in both signs). This includes pure literals.
Removing C preserves satisfiability: take any model of the remaining
formula. If it falsifies C, flip the variable of l to satisfy C. Only a
clause D containing the opposite of l could become false. The complementary
pair in the resolvent gives D a literal opposite another literal of C; it
was true and stays true. This repair need not preserve the original model,
counts, or prescribed bit values; see Järvisalo, Biere and Heule,
[*Blocked Clause Elimination*, TACAS 2010](https://doi.org/10.1007/978-3-642-12002-2_10).

Deleting clauses cannot invalidate a blocking witness for another surviving
clause. Thus clauses blocked at the same iteration can all be removed, and
exhaustive elimination is confluent: if C is removed in one complete
sequence, induct on its position to see that it cannot remain in the terminal
set of another sequence. This permits convenient deletion orders in the proof
below. Each iteration scans a polynomial number of bounded-width clause/literal
pairs, with at most the initial number of clauses many nonempty iterations.
Apply BCE *after* constructing an actual anchored OR or restricting the raw
source formula. Separate, independently simplified formulas are not substituted
into an AND or restriction on the basis of equisatisfiability.

## Why this repairs the previous tagged example

Let K be a proper width-two/three CNF on the y coordinates (as accepted by
[`tagged_xor`](../src/pnp_lab/label_controls.py)); attach one private z to
each y by t=y XOR z. The old markers attach an exactly-one constraint
on (v,a,b) to each y and z, where a,b are private to that marker. Its
positive clause (v OR a OR b) is blocked on a: its two a-negative partners
retain the complementary literal for v or b in their resolvents. Once
removed, each remaining negative clause has a pure negative helper and
is deleted. This is true after **any prefix of restrictions of the t
variables only**. No restrictions on helpers or y,z are assumed.

After removing those clauses, a complete XOR block with unassigned tag is
blocked on z: two distinct forbidden parity patterns disagree on at least
two coordinates, so opposite signs of z give a complementary pair elsewhere.
For an assigned tag one obtains the two binary clauses of equality or
disequality, with the same property. No other block or K mentions that z.
All these clauses can be removed. Equivalently, if one stops before those
deletions, the affine step can eliminate each private z by row reduction.
Confluence implies the exhaustive BCE result agrees with applying BCE to K
alone. Consequently all t-prefix residuals at a given depth (indeed at all
tag depths on the unchanged named scope) produce the same blocked+affine key.
If K has not been recognized as SAT/UNSAT, this is still a useful opaque
collision. The argument imposes no assumption that arbitrary K can be decided
by that key.

In the [reproduced control](../results/blocked_pruning.json) K is a directed
cycle of binary implications, which the existing policies leave opaque on
its own. On six tags the previous affine policy has 64 distinct keys at
the last tag depth; the repaired policy has one. With cap one, the actual
new driver maintains one unresolved representative through all six splits,
then answers SAT upon splitting a core variable. This is a family-level
mechanism, not a universal bound on the list size.

## A connected all-positive-witness obstruction for the repaired policy

For k>=1 introduce k switches s_i, a common bit h and 2k private bits
a_i,b_i. Add two ternary clauses per switch:

    (s_i OR h OR a_i) AND (NOT s_i OR h OR b_i).

For **every** nonswitch v (h, every a_i, every b_i), add two private clones
and a directed implication cycle v -> v' -> v'' -> v. The resulting connected
formula has **7k+3 variables and 8k+3 clauses**, each of width 2 or 3.
Setting every variable to true is a witness. The implication cycles force
their three vertices to have the same value; they do not restrict the
original choices.

Fix a prefix of d switches and leave the rest free. Each restriction H_A
selects, independently for each assigned position, one named binary
clause (h OR a_i) or (h OR b_i). It retains every triangle clause and the
two ternaries per unsplit position. For a fixed anchor H_A and different
H_B, let D be the positions on which their prefixes differ. The canonical
CNF of H_A OR H_B consists of:

1. All common clauses: the triangles, unsplit-switch clauses, and binary
   clauses chosen alike at positions outside D.
2. For each ordered (i,j) in D x D, the clause (h OR u_i OR v_j), where u_i
   is the A-chosen private literal at i and v_j is the B-chosen one at j.

This follows by distributivity and subsumption: a product involving a common
clause is redundant in its presence. All other products in (2) have distinct
supports, because the sets of A-chosen/B-chosen literals on D are disjoint.
None can be subsumed by a common clause. The missing A-binary clauses recover
D and hence B from the anchored CNF.

No clause is blocked. For a triangle implication, the predecessor or successor
implication gives a non-tautological resolvent on each literal, using the
fact that the three vertices are distinct. For a protected literal in a
switch clause or a product clause, a triangle clause with the opposite sign
resolves to a non-tautology because its clone occurs nowhere in that original
clause. On an unsplit switch s_i the opposite ternary also gives a
non-tautological resolvent. These witnesses still exist in every restriction
and anchored OR just described. In particular pure-literal elimination does
not remove them.

Furthermore each nonempty variable support in these CNFs has only **one**
clause; there are no units. On any width q>=2 the affine codec needs at
least 2^(q-1) distinct forbidden assignments of a fixed parity to extract
an equation. It extracts none. Thus the blocked/affine/syntax policies
all return distinct nonterminal keys across the 2^d individual restrictions
and distinct nonterminal anchored keys across the 2^d-1 partners of **each**
anchor. Equal keys between unrelated anchors would not justify the
single-anchor deletion rule. The driver therefore reaches width **2^k**
with switch-first order, and a cap W<2^k stops it as soon as 2^d>W on
that prefix (including d=0 for W=0). At k=4 the actual capped run on
31 variables and 35 clauses tries 310 anchored OR keys across levels
and reaches width 16 without any deletion.

## An UNSAT twin with the same width

A trivial SAT shortcut would notice the preceding all-true assignment. To
test the opposite answer too, keep the input and its switch order, share h
with the following six clauses, and introduce four fresh variables p,q,r,s:

    (NOT h OR p), (NOT p OR q), (NOT q OR NOT h),
    (h OR r),     (NOT r OR s), (NOT s OR h).

If h is true the first path forces p and q and falsifies the third clause.
If h is false the second path forces r and s and falsifies the last clause.
The core has no model among its 32 raw assignments; deleting any one of its
six clauses permits a model, as the experiment independently enumerates.
Every one of its literals has a non-tautological resolvent with another
core clause: on the internal path variables use the neighboring edge, on
either sign of h use an edge containing the other sign and a distinct fresh
variable. The six supports are distinct, each involving a fresh coordinate.
They cannot coincide with or subsume an old clause or be subsumed by one.

The core is common to every switch residual and anchored OR. Thus the
deletion and affine steps still have no effect, each fixed-anchor partner
list has distinct opaque keys, and every previous width and comparison
count through the switch prefix holds unchanged on this connected **UNSAT**
family. At k=4 the twin has 35 variables and 41 clauses and also returns
UNKNOWN with width 16 at cap 15, after 310 anchored comparisons. An exact
2-SAT solver on the binary subformula would already find the contradictory
paths. The twin shows that testing the all-true assignment alone does not
rescue the exhibited policy on both answers.

The proof concerns these exact policies, preprocessing and this variable
order. On the SAT family the witness is trivial; SCC-based substitution of the equivalent
triangle variables would undo the construction, and recognizing an all-true
witness would decide the SAT family directly. This is a counterexample to
these labels' universal polynomial-width claim, **not** to every possible
label, branching order or SAT algorithm.

Reproduce with `PYTHONPATH=src python experiments/blocked_pruning.py --out-dir reproduced`.
