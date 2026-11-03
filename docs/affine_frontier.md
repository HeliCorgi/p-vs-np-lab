# Deciding XOR compatibility of local supports

Choose one vector from each explicitly listed set of masks so that their
bitwise XOR equals the target. We give an exact decision algorithm, a cut-rank
upper bound on its states, and two limitations on actual images of the
[constant-block 3SAT reduction](constant_block_bridge.md). On one family a
different order restores polynomial time. On another, **every order** has a
superpolynomial explicit layer, although the source formula has an obvious
satisfying assignment. No lower bound for general SAT algorithms follows.

## 1. Absorb the groups that supply a full affine coset

Let the nonempty input supports be \(S_1,\ldots,S_g\subseteq\mathbb F_2^d\);
repetitions of an option within one support have no effect on this decision.
We want to know whether \(t\in S_1+\cdots+S_g\), with set addition over
\(\mathbb F_2\). Positive multiplicities can be discarded. An empty support
makes the answer UNSAT. With no groups the only realizable sum is zero.

Maintain the invariant that the absorbed groups realize *exactly*
\(a+U\), initially \(0+\{0\}\). Write \(q_U\) for linear reduction to
echelon normal form modulo \(U\). If \(q_U(S_i)=b+V\) is an entire affine
coset, the group can be absorbed: choose an original option \(r\) with
\(q_U(r)=b\), replace \(a\) by \(a+r\), and enlarge \(U\) by the directions
in \(V\) (in normal-form coordinates). Indeed, the already absorbed choices
supply *every* correction in the old \(U\), so each allowed normal form
contributes its entire fiber. The sum with this group is exactly the new
coset. Equality with the affine hull can be tested without enumerating the
hull: a nonempty set of size \(s\) spanning affine dimension \(r\) is the
whole coset iff \(s=2^r\). Groups that failed this test are reconsidered
when others are absorbed: a nonaffine group can become affine in a quotient.

The [implementation](../src/pnp_lab/frontier.py) records the old rank and an
original option per normal form on absorption. After selecting one original
option per residual group, the remaining correction lies in the final
absorbed span. Undo the absorptions in reverse order. If the correction is
\(e\), choose the recorded representative for \(b+q_{U_{old}}(e)\); adding
its difference from the original anchor leaves a correction in \(U_{old}\).
The invariant guarantees that this representative exists. At the start of
the absorption sequence the old span was zero, so recovery ends with zero
error. The returned choices are checked for original support membership and
target XOR. These are mask choices; recovering a CNF model additionally uses
the local assignment for each chosen mask. An input bridge preserves SAT and
witnesses, not the original number of assignments.

## 2. Filter prefix sums by what the suffix can still change

After absorption use the projected residual supports in their supplied order
and effective target \(q_U(t+a)\), denoted by \(t'\). Choose one anchor in
each residual support. For a cut after \(j\) groups let \(a_P,a_S\) be the
prefix and suffix anchor sums. Let \(P_j,V_j\) be respectively the spans of
all within-group differences from the anchors on the two sides. If a partial
sum \(p\) can reach the target, then

\[
  p \in (a_P+P_j)\cap(t'+a_S+V_j).
\]

The algorithm propagates exact prefix sums, keeping one original parent and
option for each distinct sum, and discards states outside the suffix coset.
This loses no witness: every exact suffix choice belongs to its affine hull,
and future feasibility depends on the sum, not on how it was obtained. At the
last cut the suffix is empty, so the filter requires equality to the target.
An exhausted frontier proves UNSAT; reaching a transition budget without
finishing yields UNKNOWN. On the final layer the first valid parent suffices
for SAT; there is no enumeration of model counts.

The intersection above is empty or a translate of \(P_j\cap V_j\).
Consequently the number of retained states at cut \(j\) is at most \(2^{D_j}\),
where

\[
 D_j=\dim P_j+\dim V_j-\dim(P_j+V_j).
\]

The last sum is the total residual difference span, independent of the cut.
An untouched suffix coordinate cannot change; its prefix value is forced.
The implementation keeps ordinary integer masks rather than physically
packing away those fixed coordinates. It retains old layers for witness
reconstruction, so its peak layer size is not peak memory in bytes.

If each residual support has \(s_{j+1}\) options, at most
\(\sum_j s_{j+1}2^{D_j}\) prefix/option pairs are tried. Reading and
de-duplicating the explicit input, repeated Gaussian projections, suffix
basis construction, hashing or comparing masks, parent storage and recovery
also cost work. There are at most \(g\) successful absorption sweeps and one
terminal sweep; the rank and normal-form operations take polynomially many
bit operations in the explicit input length \(N\). The state bound yields
polynomial total time for a supplied order with \(\max_j D_j=O(\log N)\)
(including polynomial dictionary costs on polynomially many keys). The
transition budget counts pairs only. It is not a wall-clock or memory bound.

Order-dependent dynamic programming has extensive precedent: see
Rina Dechter, [*Bucket elimination: A unifying framework for reasoning*,
Artificial Intelligence 113 (1999), 41–85](https://ics.uci.edu/~dechter/publications/r76A.pdf).
Its induced-width bounds concern a different algorithm and parameter. The
cut formula above and the lower bounds below are derived here for this
explicit XOR-sum representation.

## 3. A fact about crossing rows on the bridge image

Use the occurrence groups and helper triples of the constant-block bridge.
For a source variable occurring at least twice after padding, each occurrence
group has five supported masks. They live on exactly three distinct rows:
the source clause row, the outgoing equality-cycle row and the incoming
equality-cycle row. Any proper affine subspace of a three-dimensional cube
has at most four elements, so these five masks have the **entire cube** as
their affine hull. Their set itself is not affine. If all variables repeat,
no group can be the first to be absorbed. For any subset of the groups the
joint difference span is the full coordinate space on the rows it touches.
Thus \(D_j\) counts exactly the rows that meet groups on both sides of that
cut. This does not say that every point in the affine hull is reachable.

We use the following witness choices twice. For a source assignment write
\(b_v\) for the bit of variable \(v\), and give every copy of \(v\) this bit.
In each padded implication row \((\neg z,z',z')\) between consecutive copies
of \(v\), choose the outgoing helper to equal \(b_v\); choose the two incoming
helpers as \((1,1)\) for \(b_v=0\), or \((1,0)\) for \(b_v=1\). This satisfies
the three binary clauses and even parity. Each end of that row then
contributes exactly \(b_v\). **Whenever some but not all copies of a variable
are processed, at least one row of its copy cycle crosses the cut, and that
row's prefix bit is \(b_v\).** Rows belonging to different variables differ.
The helpers for a satisfied source clause are independent of these cycle
helpers: make one helper at a true literal zero and the other two one.

## 4. Two orders on the same connected UNSAT instance

Take an odd cycle of \(L=2m+1\) vertices (\(m\ge1\)); indices are modulo
\(L\). The source has two clauses for every edge:

\[
 C_i=(x_i\lor x_{i+1}),\qquad
 D_i=(\neg x_i\lor\neg x_{i+1}).
\]

Together the two clauses require opposite endpoint bits. Going around an
odd cycle makes this impossible. This connected 2-CNF has no contradictory
units, duplicated clauses, or tautologies. Apply the actual bridge, keeping
all \(C_i\) before all \(D_i\) in the source. Each source variable has six
padded occurrences. The target has \(6L\) five-option groups, \(8L\) parity
rows and \(30L\) Boolean variables.

**All positive groups first.** After all \(3L\) positive-clause occurrences
are processed, there are at least \(2^m\) retained prefix sums. Set all
even-indexed variables true and freely choose each of the \(m\) odd-indexed
bits. All positive clauses are satisfied. Choose helpers as above on these
clauses and on all copy-cycle rows. Every original variable straddles this
cut. The crossing rows expose the independent bits, hence distinguish the
\(2^m\) sums.

To see that no earlier affine filter removes these paths, use the same
copy assignment and legal local masks in the negative clauses too. For a
false negative clause, choose all three source helpers one: this violates
only its own source parity. At every cut up to the midpoint, such a row
still has a future group. Its coordinate can be flipped independently in
the suffix affine hull by Section 3. Thus a relaxed suffix completion exists
for every one of the constructed prefixes. Merging equal sums cannot remove
a distinct reachable sum. In fact this reasoning works for every model of
the positive half. The all-size result concerns the unbudgeted breadth-first
algorithm; a budget can of course stop early with UNKNOWN.

**Interleave by edge.** On the *same supports*, process the three groups of
\(C_i\), then the three of \(D_i\), before moving to edge \(i+1\). At a cut
within edge \(i\), only \(x_0,x_i,x_{i+1}\) can have copies on both sides:
all other variables have both incident edges completed or neither started.
There are at most six possibly crossing cycle rows for each such variable
and at most two partly processed source rows. Therefore \(D_j\le20\) for
every cut. Section 2 gives polynomial time on this ordered family; 20 is a
convenient bound, not an asserted optimal width. This needs no re-encoding
of the target or change to the original implication cycles.

**SAT control.** For odd \(L\ge5\), replace each negative clause \(D_i\) by
\(E_i=(x_i\lor x_{i+1}\lor x_{i+2})\). Each \(C_i\) implies its \(E_i\).
Every distinguishing assignment in the positive half now gives a *real*
completion, still with six padded occurrences for each variable. Thus a
layer can be large even if one retains only genuinely extendable prefixes.
This statement is about explicitly retaining distinct sums, not about a
search that guesses a single witness or queries an exact decision oracle.

## 5. A connected bridge family on which no reordering suffices

**Theorem.** Let \(h\ge2\) be even. On the \(h\times h\) square grid put the
positive source clause \((x_u\lor x_v)\) on every edge \(uv\); orient the
written order of each clause arbitrarily. Apply the constant-block bridge.
For *every* permutation of the resulting groups, some cut has at least

\[
                         2^{h/9}
\]

distinct prefix sums with genuine satisfying completions. In particular,
optimizing group order alone cannot give this explicit-layer decision
algorithm a polynomial bound on all reduction images.

**Proof.** Each grid vertex has degree at least two, so all local supports
have size five and no affine absorption is possible. In any group order,
take the first cut where exactly half the \(h^2\) grid vertices are
*complete*: all occurrence groups of that vertex have been processed. Such
a cut exists because a single group belongs to exactly one vertex. Call
the complete set \(P\). Of the other vertices let \(q\) be the number
*split* (some groups processed); the rest are unstarted. Let \(e\) be the
number of grid edges from a complete vertex to an unstarted one.

At least \(h\) grid edges leave a half-size set. Here is a short proof.
Every mixed row or column (containing both colors of the cut) contributes a
boundary edge in its direction. If all rows or all columns are mixed this
already gives \(h\). Otherwise there is a monochromatic row and a
monochromatic column. They have the same color where they meet; every
opposite-colored cell must lie in both a mixed row and a mixed column. If
there are \(r,c\) mixed rows and columns, then \(rc\ge h^2/2\), so
\(r+c\ge 2\sqrt{rc}\ge h\). All boundary edges go to split or unstarted
vertices, and a split vertex has degree at most four. Thus \(h\le 4q+e\).

There are two independent ways to distinguish sums at this very cut:

* The larger checkerboard color class of the split vertices contains at
  least \(q/2\) vertices and no adjacent pair. Freely set their source bits
  and keep every other vertex true. Every edge clause is satisfied. By the
  crossing cycle row property of Section 3, these witnesses have at least
  \(2^{q/2}\) distinct prefix sums.
* Set all original bits true. For each complete-to-unstarted edge, its
  source row has helpers on *both* sides of the cut. Choose the helper triple
  to be all zero, or to have one 1 on each side. Both choices satisfy even
  parity and all three local binary clauses. They change that row's prefix
  bit independently of the other edges (all helpers are fresh), giving
  \(2^e\) genuinely extendable sums.

Since \(4q+e\le9\max(q/2,e)\), the theorem follows. Good completions pass
every necessary suffix filter; all these sums must be present when the layer
is built. There are \(2h(h-1)\) source clauses, and even a dense explicit
encoding of the supports uses polynomially many bits in \(h\). The lower
bound is superpolynomial in that input length, not a claim of
\(2^{\Omega(N)}\) for bit length \(N\). It bounds the implementation's
unbudgeted explicit frontier for every fixed order, including one selected
separately for each input.

The all-true source model is immediate. This is a limitation of keeping
the entire layer of distinct XOR sums: returning a guessed and checked model
early, representing sums symbolically, changing the reduction, or branching
with an order depending on individual assignments are different operations.
In particular, the theorem says nothing about a lower bound against all
polynomial-time SAT algorithms. A possible P=NP route must decide existence
without requiring this representation to stay polynomial on every input.
