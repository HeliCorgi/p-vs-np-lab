# When a local ternary conservation test gives an actual SAT solver

[Local GF(3) hull refutation](modular_hull.md) is generally one-sided: a
consistent linear relaxation over a field need not contain a Boolean solution.
For an identifiable class of one-hot representations, the ambiguity disappears.
The [solver](../src/pnp_lab/trit_solver.py) recovers three-valued variables
(trits), checks that each of their explicitly tabulated local relations is
*equal* to its affine hull over GF(3), and solves the resulting equations.
It returns an original Boolean model for SAT, or a directly replayable raw
clause certificate for UNSAT.

## Recognition and correctness

Normalize by dropping tautologies, deduplicating literals and duplicate
clauses, keeping the original input for final checks. A signed triple
`(l0,l1,l2)` appearing as a ternary clause together with all three
pair clauses `(¬li ∨ ¬lj)` forces exactly one of its literals true.
Mark all such triples. Decline if these candidates overlap (even incompatible
orientations on the same variables) or fail to cover all variables active
in the normalized CNF. Unused coordinates of the declared input are free.

Within each detected block, order the three literals by increasing absolute
variable ID and number the selected position 0,1,2. Every trit assignment
corresponds to exactly one Boolean assignment on the active variables:
Boolean signs are respected when making the selected signed literal true
and the other two false. Conversely, any original model satisfies every
detected exactly-one constraint and therefore yields trits. There is no
assumption that the caller supplied these blocks, original edge IDs, or the
intended numerical encoding of a color.

Group the normalized clauses by their exact set of touched blocks (size
at most three), including the unary groups. On one group J, enumerate
all `3^|J|≤27` trit words and keep exactly those satisfying its raw
clauses. An empty table is inconsistent. For a nonempty table T enumerate
all normalized nonzero coefficient vectors, retaining independent equations
of the form `a·z=b` that hold everywhere on T. This finds every defining
equation of the affine hull up to linear combination: the RHS is uniquely
fixed by any one point in T, and every nonzero vector can be scaled so its
first nonzero coefficient is one. For rank r the hull has cardinality
`3^(|J|−r)`. As T lies inside, equality of that cardinality with |T|
proves that the retained equations are *sufficient* as well as necessary.
A nonaffine group causes UNKNOWN; other constraints might further restrict
that group, and no general method to exploit this is claimed.

When every group is affine of the indicated rank, combine its equations
across the whole input. Gaussian reduction and back substitution with
free coordinates zero give a concrete trit word, or a contradiction. The
former is decoded and tested on **every original signed Boolean clause**.
In the latter case the solver re-runs the independent raw-scope modular
refuter and demands a successful certificate. Why must one exist on these
inputs? Any trit value z equals `I1+2I2` over GF(3) on the three signed
one-hot indicators. Every learned trit equation thus translates to a valid
affine Boolean-coordinate equation on the union of its ≤3 blocks: signs
substitute x or 1−x. The modular finder includes this union because a clause
of that group occurs and its one-hot blocks meet the raw binary-pair
criterion. All block clauses and all constraints of that group are in its
local table. A contradiction in the trit equations still sums to 0=1
after this substitution. The same argument applies to an empty local
table. A raw empty clause is handled immediately. No consistency result
on relaxed, arbitrary field-valued indicator columns is used to accept
SAT. A SAT witness is checked without even recognizing the block structure.

For these fixed arities all local tables, independent checks, construction
and fallback raw refutation are polynomial in the explicit input length.
Grouping imposes no incidence treewidth bound. Under variable permutation,
negation or row/literal order shuffling the intended class continues to be
recognized provided the exact-one partition remains unambiguous. The
numbering of colors within each block can be independently permuted:
*all six permutations* of GF(3) are affine. The six distinct functions
`t ↦ a t+b`, a∈{1,2}, b∈{0,1,2}, exhaust them. Thus affineness and
consistency do not depend on recovering the original per-edge color ordering.

## Checks and the boundary

The [tests](../tests/test_trit_solver.py) classify all 512 possible binary
trit relations against an independent closure test `x−y+z∈T`, verify
decoded witnesses and tamper with proofs. The signed-scrambled prism
[experiment](../results/trit_solver.json) supplies no witness to the
solver. At k=128 it recovers 384 trits and 640 local groups from 1,152
Boolean variables and 6,144 clauses, with 256 affine equations and global
rank 255. In the balanced case it constructs a Boolean model and checks
every clause; the unbalanced instance produces an independently checked
GF(3) raw-CNF contradiction.

Recognizing three-state blocks by itself cannot give a polynomial-time
general SAT algorithm. Standard graph 3-colorability is NP-complete
([Garey, Johnson and Stockmeyer](https://doi.org/10.1016/0304-3975(76)90059-1)).
Give each vertex one block and for each edge forbid the three matching
colors by three binary clauses. The pair table has six points; its affine
hull is the full plane of nine. With at least one edge the specified
procedure therefore declines, whether or not the graph is colorable. This
is an NP-complete image using just one fixed nonaffine binary relation and
the elementary domain encoding. In the finite control K4 has no Boolean
model and K4 minus one edge has six; both return UNKNOWN. This is not a
lower bound for every solver on these small graphs or a resolution of P
versus NP.
