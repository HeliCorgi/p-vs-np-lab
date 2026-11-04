# A resolution lower bound inside the previous blind encoding

The phase-12 [distinct-support 3-CNF](split_parity.md) did not merely mask
literal signs from the root parity pass. Ordinary resolution can still need
linear width and exponential proof length there, even for a **positive unit
consequence of a satisfiable instance**. There also exist two children of
one blind 3-CNF such that *every* signed-literal/constant map in one
direction requires exponentially many ordinary-resolution justifications
in total (or has no such certificate). Neither statement rules out fast
semantic reasoning, the opposite direction, a known constant witness on a
SAT target, or arbitrary proof systems.

## Which measure and calculus?

Clauses are sets of literals. A line is an input clause, binary resolution
of two earlier lines on opposite pivot literals, or weakening (adding
literals). Width is the greatest number of literals on **any** used line.
Length is the total number of lines, allowing unrestricted DAG reuse; a
bound on length does not bound the time needed to find a proof. No new
extension variables/definitions or XOR proof rules are allowed. The primary
source for the asymptotic hard seed is Ben-Sasson and Wigderson,
[*Short Proofs Are Narrow—Resolution Made Simple*](https://doi.org/10.1145/375827.375835),
[paper, Theorem 4.4 and Corollary 4.5](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf).
The odd Tseitin CNFs H on connected cubic expander families (one Boolean
bit per edge) have width Ω(t) and require exponentially many lines in t,
where t is the number of graph vertices. These are width-three formulas
with O(t) clauses and variables. There is no suggestion that deciding
parity itself requires exponential time: linear algebra decides H directly.
Weakening need not appear in a refutation (one may keep stronger
subclauses instead), so the stated convention does not evade the lower
bound.

## Why identifying variables in a proof is legitimate

A substitution maps every variable of a formula to true, false or a signed
variable of another formula. Pull back a clause: discard false constants,
collapse repeats, and mark it TRUE if it contains a true constant or a
complementary pair. Suppose every axiom of G pulls back to TRUE or to a
clause containing an axiom of H. A refutation of G yields a refutation of H
of **no greater width and no more lines**. The same construction works if
the required source subclauses already have proofs: start with their DAG
and add at most one line per subsequent target line.

Keep a derivable **subclause** of the image of every nontrue line; skip
true lines. Axioms and weakenings satisfy the invariant immediately. Write
the parents of a resolution step as p∨U and ¬p∨V, its conclusion U∨V.
If the conclusion is nontrue, neither U nor V pulls back to true. If the
pivot is constant, use the parent with false pivot. With a (possibly
negated) variable pivot l, if one parent maps to TRUE, its nonpivot part
must contain the opposite of its pivot; the *entire* other parent's
nontrue image is then contained in the conclusion. If both parents are
nontrue and one derived subclause already suffices, reuse it. Otherwise
they contain opposite mapped pivots; resolving on those yields a subclause
of the desired image. Width never rises, even for noninjective maps.
The empty clause neither becomes true nor has a proper subclause.

In the simple-support encoding E(F), set all six gadget bits true (one of
the two allowed words) and the two trailing padding bits true. Identify
each occurrence copy with its own source variable, respecting the original
sign on the occurrence. Every wiring cycle/padding clause becomes true;
the nontrivial images of the occurrence clauses are exactly the
normalized original clauses. Hence width(E(F))≥width(F) and
size(E(F))≥size(F) for UNSAT F. This is a width/length statement about
this specific calculus, not a general property of equisatisfiable CNFs.
The [trace translator](../src/pnp_lab/width_transfer.py) checks pivots,
maps constants/literals and emits ordinary resolution without needing
weakening in its translated proof.

## A single unit implication from an explicitly satisfiable source

Take a seed H. Add a logical switch s. Guard every clause c as s∨c. For a
ternary c=(a∨b∨z) keep width at most 3 by introducing a fresh y and using
(s∨a∨y) and (¬y∨b∨z). Encode the whole result with E. Choose one named
occurrence copy s* of s. The encoded formula has a known satisfying model:
s=true, every ordinary variable and every fresh y=false, all copies
consistent, the gadget bits and the trailing padding bits true. It entails
the positive literal s* exactly when H is UNSAT (the other branch is H
up to existential auxiliaries). For odd Tseitin H it therefore entails a
particular unit even though finding a satisfying assignment to the source
is easy.

In the proof substitution, set s=false and set every split helper y=¬a.
The first half of its clause becomes tautological; the second becomes
exactly c. Combine this with the occurrence-copy/padding substitution above.
A proof of s* projects to a refutation of H since s* maps to false. A
proof from the extra assumption ¬s* yields the same conclusion (that
assumption becomes TRUE). Thus proving this **specified target clause**
requires Ω(t) width and exp(Ω(t)) ordinary-resolution length. In particular
the identity model map to the target (s*) is valid but expensive to
justify in this way. Setting the target to true instead is a trivial valid
constant map; this example does not rule out all maps.

## One hard direction for every substitution between actual siblings

For the stronger direction claim, add (¬s∨p) and (¬s∨¬p) with fresh p
**before** applying E. Now both s*-children A (false) and B (true) of the
same final, distinct-support 3-CNF are unsatisfiable when H is. Setting p
false along with the previous substitution still projects every axiom of
A to H or TRUE, because ¬s is true. Thus A inherits the above lower bounds.

B has an ordinary resolution refutation of width at most 6 and O(t)
lines. First derive the three positive units on forcing bits 4, 5 and 6.
For each unit falsify it and branch on the remaining five gadget bits;
at each leaf choose a falsified ten-clause-gadget axiom. Going back up,
resolve on the split bit when necessary; the resulting subclause contains
only literals falsified by the remaining partial assignment, so width is
at most 6. This is a constant proof constructed and replayed, not a
trusted truth-table axiom. These units remove all false padding literals.
The s* assignment now propagates around the directed cycle of s copies.
The two additional guarded clauses force opposite values on the two p
copies; their equality implications propagate the contradiction. Each
propagated unit follows from a width-at-most-three original clause by at
most three single-pivot resolutions. The explicit refutation has length
O(t). B remains easy in this sense regardless of H.

Fix **any** proposed map from A-models to B-models given by constants or
signed source literals on target variables. If its nontrue, pulled-back B
clauses all have ordinary-resolution proofs (derivations of subclauses
also suffice) from A of maximum width W and total DAG length S, transport
B's short refutation through this map. By the substitution lemma, A would
have a refutation of width ≤max(W,6) and length ≤S+O(t). Thus W=Ω(t) and
S=exp(Ω(t)) on the seed family. Purely semantic model transport is
vacuous on these UNSAT branches; the obstacle is certifying it in the
specified proof language. The reverse direction is **not** obstructed:
B's easy empty-clause proof justifies every target there. Do not infer an
exponential search-tree width for a solver able to discard B, or able to
apply other proof rules.

For the implemented shallow case-split plus unit checker, a proof of a
pulled width-three clause C at split depth d has an ordinary-resolution
simulation of width ≤3+|C|+d≤6+d. At a leaf, the assumptions are the
negation of C and at most d decision literals. Unit reasons are inferences,
not extra decisions: replay the unit resolutions under these assumptions
at width ≤3. Discharge the assumptions by adjoining their complementary
literals (or keeping subclauses) to every local line; the leaf establishes
a clause on just C and the negations of its branch decisions. Derive these
leaves separately, including inherited unit reasons along each path. At an
internal decision resolve the two child clauses on the split literal, or
reuse one if it already implies the parent goal. This covers direct
subsumption and tautology certificates as well. Allowing arbitrary ordinary
RUP sequences with intermediate lemmas of *unbounded width* is a different
policy; short sequences with standard unit reasons still give ordinary
resolution proofs with polynomial overhead, so the length barrier matters
too. None of this bounds certificates using definitions, extended
resolution, or unrestricted algebraic inference.

All encodings are O(t) in numbers of variables and clauses, or O(t log t)
bits in a binary literal-index format. The width and length lower bounds
are measured in t, not necessarily in the printed bit length with the same
exponent.

## Reproduction and evidentiary limits

[Experiments](../experiments/width_transfer.py) and [report](../results/width_transfer.json)
check every nontrue hard-branch axiom image, verify original satisfying
words for the unit-consequence variant, and replay a generated easy-branch
refutation on K4 and three cubic prisms. These small graph choices are not
an experimental claim that prisms form expanders. On K4, complete
width-three saturation finds exactly 16 clauses and no contradiction; the
width-four trace does refute it, giving the exact finite minimum 4. The
smallest two-unit control also translates a concrete 76-line proof to a
3-line source refutation. The infinite family lower bounds come from the
cited theorem and the proof transformation, not curve fitting or timeouts.
