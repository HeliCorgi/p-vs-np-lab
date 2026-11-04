# Summing punctured affine flats without listing their points

A three-point support over the binary field consists of three corners of
a four-point affine plane. Instead of trying to remember or match all
possible prefix sums, we store the plane and its **one missing point**.
Some sums of these sets admit exactly the same representation at arbitrarily
large rank. This gives a polynomial-time *partial* SAT decision procedure:
SAT answers contain original choices, and UNKNOWN is not a negative answer.

## The merge identity

Let the two affine hulls be `a+P` and `b+Q`. In each, either all points
are present or one specified **absolute** point is missing. Call their
represented subsets A and B, and put `H = P ∩ Q`, of dimension k.
For each point w in the sum hull `a+b+(P+Q)`, choose one decomposition
`w = x+y` in the two hulls. All hull decompositions are

`(x+h, y+h)` for every h in H,

with addition denoting XOR. They are all distinct and exhaustive: the
differences of any two decompositions are equal and belong to both direction
spaces. Therefore **one missing point on either side excludes at most one
of the possible decompositions of this fixed w**.

* If both sets are full, their sum is the full sum hull.
* If k≥2, the fiber has at least four choices. At most two are excluded,
  so the sum is full. For k≥1 even a two-point fiber suffices when at most
  one side has a hole.
* If both sides have holes u,v and k=1 with nonzero common direction h,
  their sum is **the full sum hull minus precisely u+v+h**. At that
  target, the two decompositions are `(u,v+h)` and `(u+h,v)`, both
  excluded. At any other target simultaneous exclusion of both fiber
  points would require two different decompositions involving u and v.
  They would differ by h in each coordinate, forcing the same target
  u+v+h. In particular u+v itself is present via `(u+h,v+h)`.
* For disjoint directions (k=0), two punctured positive-dimensional
  flats need not have a one-hole sum. The algorithm leaves such a pair
  separate. Translating a set by a full singleton is always valid.

For three distinct vectors x,y,z the input flat has anchor x, directions
x+y and x+z and hole x+y+z. Adding the hole makes it a full plane. Two
points or a singleton are already affine. The implementation first uses
the lab's existing [exact affine quotient and lifting](affine_frontier.md),
so only ternary groups remain for the pair loop. This preliminary reduction
can absorb formerly nonaffine groups if they become affine in the quotient.

## Turning the identity into a decision and a witness

[`decide_hole_flats`](../src/pnp_lab/hole_flats.py) joins a legal pair,
remembers its two children, and repeats in a deterministic first-fit order.
No property of an optimal merge order is assumed. For each sum it stores
a basis of P+Q, a particular-decomposition map and up to two independent
vectors of H. These suffice to reconstruct a witness: for any requested
**present** sum w, try its particular decomposition, then those shifted
by each stored common vector. There are at most two forbidden decompositions
and, when k≥2, these three candidate decompositions are distinct. At least
one candidate succeeds whenever w belongs to the represented sum. Repeat
down the merge tree and then undo the original affine quotient. The returned
masks must belong to their own original supports and XOR to the input target.

The maps are elementary tagged Gaussian elimination. Insert P's basis
vectors with themselves as tags, then Q's with tag zero. Eliminating a sum
adds the corresponding tags and supplies its P component; the remaining
component is in Q. Whenever a new Q direction reduces to zero, the tag
of that dependency supplies a vector in H. These vectors are independent:
each dependency has a different last inserted Q basis variable, and the
tuple of Q coefficients determines the common vector injectively since
Q's basis is independent. Their number is precisely
`dim(P)+dim(Q)-dim(P+Q)`.

At the end, solve the affine equation on the remaining flats' local
direction coefficients. Failure proves UNSAT. If its solution is unique
and hits a missing point, that also proves UNSAT. Otherwise a particular
solution avoiding every hole proves SAT and can be lifted. In the default
pair-only mode, if the particular solution hits a hole and alternative
decompositions exist, return UNKNOWN. Pairwise trivial intersection is not
the same as a direct sum of *all* remaining direction spaces.

With `cover=True`, the last unresolved fiber also gets an
[exclusion-count test](../src/pnp_lab/flat_cover.py). Each individual hole
forbids a computable number of affine decompositions. If their sum is
*strictly* less than the number of decompositions, some assignment must
avoid all holes. Conditional expectations can find one without testing
every parameter assignment. The bound is sufficient, not necessary:
the bad events may overlap. An individual forced hole is itself decisive.
Any returned flat values still have to be lifted to original checked masks.

All these pair operations have polynomial **bit** cost in the explicit
input length. There are at most g−1 successful joins for g groups and
at most O(g³) tested pairs even with full rescans. Gaussian elimination
uses at most the explicit ambient rank and works on vectors and tags of
polynomial bit length. The tree stores only polynomially many basis rows,
not a list of the points of each flat. Reconstruction visits each merge
once. These are bounds on the partial algorithm, not on some later exact
fallback needed to replace UNKNOWN for every input.

## Controls: non-graphic and high-rank sums

Three supports `{0,1,2}`, `{0,1,4}`, `{0,1,6}` have all seven nonzero
3-bit masks as pair differences. Their difference matroid is the Fano
matroid, so the [global graphic recoding](graphic_gauge.md) cannot work.
The first two planes meet on direction 1; their sum is a rank-three flat
with one hole. The third plane lies in that three-space, so the second
join fills the hole. Every target in the space has a checked witness.
This example is a generic support instance, not an assertion about all
Fano minors of sparse 3SAT images.

For arbitrarily large m, use groups `{0,1,2^j}` for j=1,...,m. At each
join the new plane and the accumulated hull meet on direction 1. The
combined hole after j groups is the all-ones (j+1)-bit mask, by the
one-dimensional rule; the other `2^(j+1)-1` targets are present.
At m=256 the experiment checks the absent target and a present target.
Adding one more group `{0,1,6}` (m≥2) makes the entire 257-bit space
reachable when m=256, with a Fano restriction on the differences.
These set sizes are deduced from the identity, not observed by enumerating
that many points.

A separate control uses planes on independent coordinates P,Q and their
diagonal, with supports `{0,1,2}`, `{0,4,8}`, `{0,5,10}`. No two planes
intersect nontrivially, but their three-way decomposition kernel has
dimension two. At each target there are four affine decompositions;
every flat hole excludes just one of them. Thus all 16 targets are SAT,
including those on which a first particular decomposition hits a hole.

## Where even a complete scan for mergeable pairs stalls

Use the [phase-six sparse constructor](support_threshold.md) on a formula
with m≥1 clauses of exactly three distinct variables each, where each of
the n used variables occurs at least three times; put ℓ=3m. Clause signs
can be arbitrary. After contracting the ℓ binary copy directions, value
masks for a variable are consecutive edges of its private occurrence
cycle. Each is nonzero. Since the cycle has length at least three, these
are distinct binary vectors, including within each variable. Write V_j
for the resulting value direction of occurrence j and C_j for its unique
literal-selection coordinate. The occurrence planes have direction spaces
`span(V_j,C_j)`. Two different such spaces meet only in zero: their
selection coordinates differ and no two V's are equal. A clause-selector
plane consists of even-weight combinations of three private C coordinates.
It meets no occurrence plane nontrivially, and planes of different clauses
have disjoint coordinates. All groups still have three distinct options
and none is further absorbed. **There is no first legal pair join.**

The affine relaxation nevertheless always has solutions. Assign arbitrary
source bits and choose any of the four odd-parity triples at each clause
(including the all-ones triple forbidden by the true three-option selector).
Each occurrence's relaxed local pair then agrees with both its source bit
and its clause-selection bit. Conversely, copy equalities and port agreement
determine all local choices from these parameters. Contraction of the
independent binary copy directions loses no multiplicity here: any consistent
residual tuple fixes the copies uniquely. Thus there are exactly
`2^(n+2m)` affine decompositions. Each clause group sees its four corners
uniformly. For each occurrence the independent source and selector bits
also see all four corners uniformly. Hence each one of the `ℓ+m=4m`
holes excludes exactly a quarter of the fiber. Their exclusion sum is
**m times the entire fiber size**. A strict first-moment bound therefore
cannot certify SAT on this class, even though some particular solutions can
avoid all holes. For UNSAT inputs no checked candidate can succeed and no
individual hole is forced; both modes return UNKNOWN.

This no-merge restriction still admits general 3SAT. Start with distinct
clauses of exactly three distinct variables (discard tautologies, remove
literal repetitions, pad a binary clause with both signs of a fresh
variable, pad a unit clause with all four sign patterns of two fresh
variables; an empty clause can be handled separately). For each original
variable x in this normalized formula append the four clauses
`(x,u,v), (¬x,u,w), (x,v,w), (u,v,w)` on three fresh private variables.
All added clauses can be satisfied by setting u,v,w true, and none changes
the truth of an original clause. The occurrence counts of x and all fresh
variables are now at least three; no duplicated clause is needed. The
transformation is polynomial. Thus the limitations concern a subclass
that still covers general source satisfiability, not just small examples.
They apply to these specific pair and strict exclusion tests, not to every
symbolic algorithm.

The [reproduction report](../results/hole_flats.json) separates these
proofs from the finite checks: among other controls, on all 512 signings
of the three-clause Fano source the pair-only mode returns 256 directly
verified SAT witnesses and 256 UNKNOWN answers. An original source oracle
confirms that all these formulas are satisfiable.

## Lean scope

[`Formal/HoleFibers.lean`](../Formal/HoleFibers.lean) proves that three decompositions with distinct lefts and distinct rights survive two single-point exclusions, characterizes blocking on a two-decomposition fiber, and proves the XOR exceptional-target formula given the closure and exact two-point-fiber hypotheses. It does not verify the echelon computations, Python program, matroid-minor construction or its running time.
