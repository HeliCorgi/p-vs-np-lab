# What a one-way map buys, and why complete map discovery is difficult

A certificate for A → B takes a model of A and builds a model of B. A diagonal
flip is the very special map b_i = a_i XOR e_i, including negative literals
but neither renaming nor constants. The tests below use the actual checked
[map finder](../src/pnp_lab/witness_transport.py) and
[frontier](../src/pnp_lab/decision_pruning.py). A pair of unequal labels by
itself justifies no deletion.

## A directed sibling, repeated k times

Use independent tags t_i, variables a_i coupled by any 3-CNF K(a), and z_i.
Add the three clauses

    (t_i OR a_i OR z_i)
    (NOT t_i OR NOT a_i OR z_i)
    (NOT t_i OR a_i OR NOT z_i).

With t_i=0 the local requirement is a_i OR z_i (weak); with t_i=1 it
is z_i=a_i (strong). From strong to weak, **flip z_i**, leaving a_i
alone. In the pulled-back weak clause the result a_i OR NOT z_i is an
actual strong-source clause. Literal identity fails even with empty K
because the strong pair allows 00. On these two isolated bits the
reverse direction cannot use a diagonal flip: a bijection cannot take
three satisfying points into a two-point set. This does not exclude a
noninjective map or a constant witness for a satisfiable target.

For controls that should survive the previous simplifications, put
NAE(z_i,p_i,q_i) on two private helpers per block (one positive and one
negative ternary clause). For each nontag bit v, add two private clones
and assert pairwise equality on a triangle by two binary implications
per edge. This adds no restriction on old assignments: given z, the two
helpers can make NAE true; the clone bits copy v. When flipping z_i,
flip both NAE helpers as well (NAE is invariant under simultaneous
complement) and the six clone bits of these three variables. This is a
nine-coordinate simultaneous substitution, valid for **any** K; it
fixes all the a-coordinates. Other siblings and unassigned tags are
unchanged.

There is also a discovery argument, not just a manually supplied map.
For proper uniform width-three K (three distinct a variables per
clause), each K-support sees the same set of clause signs on both
sides and has no smaller source support that could subsume it.
Its allowed local translations are the stabilizer of that set. The
same holds for unchanged tag/NAE/triangle supports: no triangle
clause relates two distinct original gadget coordinates, and every
other gadget has at most one a coordinate. On the changed (a_i,z_i)
support the shifts have odd parity so the weak forbidden point is
translated to one of the two strong forbidden points. Thus all local
admissible flip sets are affine and the joint system is feasible by
the explicit flip above. The existing linear-system pass finds a
certificate without trying all subsets of flipped bits. Empty K
is also allowed. The semantic map for arbitrary K is not a claim of
complete automatic discovery under arbitrary extra overlapping clauses.

Consequently, on tag-first branching, the two children of a retained
prefix can always be thinned to one, for that uniform-core family.
If a label already settles a branch or merges it, there may be even
less work. This bound is only on these **k levels**. With t gone the
remaining decision is still exactly SAT(K): choose z=1 for weak and
z=a for strong, followed by marker witnesses. Since proper 3-CNF cores
can be NP-complete, no uniform bound for the core follows.

The concrete K in the [report](../results/witness_transport.json) is a cycle
of NAE constraints on overlapping triples. At k=4 and 6 the experiment
checks all 78 sibling pairs across both full tag trees, not merely pairs
visited by the pruned traversal. With either syntax or blocked labels,
anchor-OR comparisons disabled and a cap of one, the old driver stops
at the first tag; with the flip finder it retains width one all the way
through the tags, then returns UNKNOWN at the first core split. Raising the
cap to eight lets the k=6 run return SAT. We do not count that as a
width-one decision for the whole formula.

## Retest on the previous phase's connected SAT/UNSAT twins

The same report reuses exactly the [previous shielded switches](blocked_pruning.md),
without changing their clauses or branch order. With k=4, cap 15, blocked
labels and anchor-OR comparisons enabled, the baseline returns UNKNOWN
on both. Adding the default discovery policies returns SAT on one and
UNSAT on the other. Equal-size/name-permuting sibling swaps are useful
here; this is distinct from the strict strong-to-weak block above.
The old SAT twin even has an all-true witness, and its UNSAT sibling's
binary subformula already exposes a contradiction to a 2-SAT solver.
These are regression controls, not intrinsically difficult SAT benchmarks.

## NP-complete even for diagonal flips between siblings

**Decision problem.** Given an explicitly listed Boolean variable scope, a
3-CNF F and its designated tag s, ask whether there exists a sign mask
whose diagonal flip passes the raw clause-tautology/subsumption check from
F restricted by s=1 to F restricted by s=0. It is in NP: one sign bit per
coordinate, at most three literals per target clause, and polynomial-time
verification. If s is retained as an unused coordinate in the residual
representation, its flip is immaterial.

Given any 3-CNF B, make the target restriction a projection-equivalent
copy of B. For a short clause C of width at most two add (s OR C).
This includes an empty C. For each length-three clause (l1 OR l2 OR l3),
use a fresh variable w exclusive to that clause and add

    (s OR l1 OR w) AND (NOT w OR l2 OR l3).

For every original variable x and every helper w add (NOT s OR NOT x)
or (NOT s OR NOT w), respectively. Width stays at most three and the
construction has linear overhead in the number of variables and clauses.

* At s=0 the pins disappear. The two clauses with w admit an extension
  exactly when the corresponding clause of B is true: w=0 works if l1
  holds; otherwise w must be 1 and l2 or l3 must hold.
* At s=1 every nontag bit is pinned to zero. Every remaining clause
  (NOT w OR l2 OR l3) is then satisfied automatically.
* If a checked flip exists, apply it to this known zero assignment.
  Soundness gives a target assignment and hence a B model.
* Conversely, use any target model y. Flip exactly its one-coordinates.
  For every target clause at least one true target literal pulls back
  to a negative source literal, hence its negative unit pin subsumes the
  pulled-back clause (or the clause is already tautological). So this
  is a **syntactic** certificate, not just existence of some map of
  source models. The argument survives ordinary tautology deletion and
  subsumption normalization on these inputs.

Thus B is satisfiable iff a certified diagonal flip exists. This directly
reduces 3SAT to our precise discovery problem without constants, permutation,
or ruling out nonuniform formula families. It does not say a SAT solver
must search complete substitution space: a partial polynomial finder can
help, and another pruning method might establish a universal width bound
without completeness. The [test and experiment](../experiments/witness_transport.py)
also check each of 3,784 explicit sign masks on 42 small control formulas
against truth-table semantics; the proof, not that enumeration, supplies
NP-hardness.
