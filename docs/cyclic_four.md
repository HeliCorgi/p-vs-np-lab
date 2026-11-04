# Recovering a cyclic order-four law without state names, and checking 0=2

Four-state Boolean domains can represent different algebraic structures. The
[native solver](../src/pnp_lab/cyclic_four.py) tries a specific hypothesis:
local interactions are *ternary cyclic addition relations* on signed
one-hot blocks, over the ring of integers modulo 4. It does not assume
that the given order of the states is the cyclic order, and does not
divide by a nonunit. SAT is accepted only on an original Boolean model;
UNSAT only by an independently replayable modular sum. See the
[prism experiment](../results/four_flow.json) for flow controls.

## Domain and relation discovery

The input is a width-three CNF with signed one-based literal IDs. As in the
trit solver, duplicates and tautologies can be removed for discovery only.
Find two ternary clauses `(a OR b OR h)`, `(NOT h OR c OR d)` and the six
binary at-most-one clauses on a,b,c,d, where the four state literals and
one helper variable are distinct. Require the helper to occur only in this
complementary pair of clauses. Then exactly one state literal is true and
h is uniquely determined: it is true precisely when c or d is chosen.
This rule works with signed indicators, variable-index scrambling, swapped
helper signs and arbitrary reordering. Decline ambiguous overlapping
blocks or active bits not covered by the detected blocks. Mark the
original clause IDs proving each recognized domain.

Number the slots of each block by their absolute indicator IDs, temporarily
0 through 3. Group raw clauses by the set of touched blocks. On a group
of at most three blocks, tabulate the valid slot words, including the
required helper values. A full table is irrelevant, and an empty one
gives a locally proved contradiction. For each other table require three
distinct blocks. Seek local bijections p,q,r onto Z/4 and a right side b
such that the table equals exactly

    p(i) + q(j) + r(k) = b  (mod 4).

Normalize p(0)=q(0)=r(0)=0: subtracting additive constants just changes
b. Thus there are 6^3 possible triples, each on at most 64 words. The
proposed law has exactly 16 solutions (every pair extends uniquely), so
testing inclusion and cardinality suffices. Unary/binary nontrivial
tables and other ternary tables are conservatively declined. In particular
the solver is not a general four-state CSP algorithm.

Unlike the trit case, an arbitrary permutation of four states need not be
affine over Z/4. Local calibration is needed. For a valid addition table,
any two normalized representations differ by the **same unit multiplier**
u=1 or 3 across all three coordinates. Indeed, compose each second bijection
with the inverse of its first bijection to get maps F,G,H of Z/4. Fix any
x,y and the required z=b−x−y. Replacing (x,y) by (x+1,y−1) while holding
z fixed shows F(x+1)−F(x)=G(y)−G(y−1). Thus their increments are the same
constant for all independent x,y. Repeat with x,z to obtain that same
increment for H; normalization fixes the three offsets to zero. A bijection
of a cyclic group with constant increment must have a unit increment. The
solver therefore chooses one canonical representative of each local
bijection up to sign and requires agreement on every shared state block.
Signs become coefficients ±1 in its global linear system. This test
accepts arbitrary independent relabelings of the four colors on a
coherent network of such constraints, including different color orders on
different edges. Two individually recognizable relations can impose
incompatible cyclic coordinates and will be declined.

## Linear solution and independently checkable refutation

With a unit coefficient pivot, normalize by its inverse (1 or 3), eliminate
its column and save the pivot equation for back substitution. If no unit
pivot remains, every coefficient is 0 or 2. An odd RHS in such a row need
not itself have zero left side, but **twice** this row is exactly 0=2. If all
RHS values are even, the residual system asks for a binary linear relation
on the low bit of each variable. Subtracting even rows with the same
pivot 2 eliminates that pivot without treating 2 as invertible. It gives
either a constant contradiction or a Boolean low-bit solution: divide
the even congruence by two only to read it *over GF(2)*. The unused high
bits may be set to zero. Back-substituting into saved unit rows recovers
a full word in Z/4. Invert each calibrated state permutation, set every
indicator and its private helper, and directly evaluate every original
clause before returning SAT.

On UNSAT record row combinations using weights in the **original** ring,
including multiplication by 2 in the odd-RHS/only-even-coefficients case.
To translate a calibrated state value to raw Boolean coordinates, weight
the four signed indicator literals by their calibrated residues; exactly
one indicator is true. Replacing a literal 1−x adjusts the coefficient and
the RHS. Hence cancellation of the coefficient on each calibrated block
implies cancellation on all original Boolean columns as well. A certificate
contains those scaled Boolean rows, each with at most 15 cited-scope bits
(three domains of four indicators and one helper) and original clause IDs.
A separate checker enumerates local Boolean truth tables via bitsets,
evaluates the two bits of the mod-4 sum including carry, and verifies that
every assignment accepted by the cited clauses satisfies the claimed row.
It then checks that adding them gives zero in every column and a **nonzero**
constant mod 4. This last step proves a contradiction even for 0=2, which
cannot be rescaled to 0=1 in this ring. No state label recovery or Gaussian
elimination runs inside the checker. The Fin 4 corollary in
[Lean](../Formal/ModularHull.lean) formalizes this final conditional
summation implication, not the Python parser/solver.

For fixed arity, modulus and block size the number of local candidates,
words per table, and bits per verification scope are constants. Discovery,
table certification, global elimination, proof construction and replay are
all polynomial in the explicit original input encoding. There is no
all-input completeness bound outside the recognized representation. The
[tests](../tests/test_cyclic_four.py) exhaust actual state words for 250
small modular linear systems, including nonunit pivots, independently check
scrambled models/refutations, and reject a Klein-four law and a pair of
incompatible calibrations.
