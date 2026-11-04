# Exact Boolean correlations: join before projecting

The 31-variable, 152-clause core from phase 15 has a refutation using **union
scopes of at most five original variables**. Every step is checked by explicit
Boolean tables. A restriction to union scopes of at most four cannot refute
this core in the exact join/project calculus defined here. Thus its minimum
union width is exactly five. This is a finite proof-system statement, not a
polynomial-time algorithm for all SAT instances.

## 1. What is preserved

A relation consists of a sorted subset `S` of the original variable labels and
a bitset for its allowed words in `{0,1}^S`. Bit `j` of a word is the value of
the `j`th variable in the scope. The input relation of a clause is its actual
satisfying truth table.

To combine `R` on `S` and `Q` on `T`, enumerate one assignment on `S ∪ T`,
require that both restrictions belong to their relations, and then project
existentially onto a specified subset of `S ∪ T`. Shared coordinates have one
value. Taking independent existential witnesses on the two sides can lose the
very correlation needed to detect a contradiction: equality and disequality
both project to a full unary domain, although their join is empty.

The [checker](../src/pnp_lab/relation_proof.py) reconstructs every original
clause table and every join/projection, and accepts only an empty final
relation. It does not invoke resolution, the search procedure, or an integer
solver. The compiler uses a checked resolution DAG to propose the tables;
the semantic replay checks the resulting operations independently.

## 2. The finite result and its cost

The [experiment](../experiments/correlation_relations.py) replays the original
core and one signed permutation. The original proof contains 115 input nodes
and 253 joins, for 368 nodes total. Stored relations have at most four
coordinates, but a join can temporarily use five. Across the whole replay,
the checker enumerates 6,398 union assignments and stores 3,659 truth-table
cells; the compact JSON certificate occupies 25,890 bytes.

The first retained binary clause is `x23 ∨ ¬x30`. Its table permits words
`0, 1, 3` on scope `[23,30]` and forbids word `2`. These three points have the
full integer affine lattice: their differences generate `(1,0)` and `(0,1)`.
Consequently, converting this learned relation back to its integer affine
hull would erase its only restriction. Keeping the actual forbidden pair
matters even after it has been discovered. Its derivation uses 13 original
clauses; it is not visible in any one original clause profile.

These replay counts exclude discovery. The resolution finder stores 26,826
clauses and visits 180,420 candidate pairs, with further subsumption and
deletion work recorded in [the resolution report](../results/correlation_resolution.json).
A short final proof does not imply a comparably cheap way to find it.

## 3. Why four-variable unions cannot suffice here

A proper linear 3-CNF has three distinct variables per clause and at most one
shared variable between any two distinct clauses. In particular, repeated
unsigned supports are excluded, and a set of
four variables contains at most one original clause support.

Consider derivations starting from these original clause relations and full
cubes, using only exact join and existential projection on original
coordinates, and charging the full parent union of each join. With union
width at most four, every relation is a full cube or a cylinder of one
original clause whose entire three-variable support is still present:

1. This holds for the input tables and full cubes.
2. Projecting away a variable of that clause makes its relation a full cube;
   retaining its whole support preserves that same clause cylinder.
3. Joining full cubes or two copies of the same clause cannot add another
   restriction. Joining different original clauses requires at least five
   variables, by linearity, and is prohibited at width four.

All such relations are nonempty. This proves the lower bound independently
of the search cap. The checked union-five proof gives the matching upper
bound. The statement excludes branching assumptions, extension variables,
arbitrary semantic consequence rules, and extra externally supplied lemmas.

Ordinary resolution is a special join/project operation: joining
`x ∨ A` and `¬x ∨ B` and eliminating `x` yields `A ∨ B`. A width-four resolvent
may therefore require a five-variable intermediate join. Width conventions
cannot be identified without this extra coordinate.

## 4. Formal and computational scope

[Four Lean theorems](../Formal/CorrelationProof.lean) establish semantic
soundness of derivations, refutation by an empty relation, the exact
join/projection identity for resolution, and the loss from separate
existential witnesses. The semantic `table` constructor requires a proof of
its implication; it is not an oracle granting arbitrary consequences.
Lean does not verify the Python code, the finite certificate bytes, or the
width-four lower-bound argument above.

The Python checker has explicit node, union-width, and table-cell caps.
Guide validation is also bounded by the source node count, actual reconstructed
width, and cumulative literal occurrences, before table compilation. The table
implementation caps union width at 12. Exceeding a compilation
budget returns `UNKNOWN` with no proof, and a checker rejects over-budget
certificates. The finite bounds are reproducible with
`python scripts/reproduce.py --out-dir reproduced --check`.

For known width games, polynomial calculus, local distributions, and the
asymptotic boundary, see [the proof-system comparison](correlation_proof_boundary.md).
