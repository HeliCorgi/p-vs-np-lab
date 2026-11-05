# A family on which learned clauses unlock a global integer contradiction

The old [private chains](modular_padding.md) had an elimination pivot at every
step. The new [fixture](../src/pnp_lab/feedback_fixture.py) replaces a single
chain by a layered directed graph. On the parity examples the raw integer
pass emits no rows, the old private-pivot peeler makes no move, yet the
[feedback learner](integer_feedback.md) recovers every core clause from the
raw CNF. An integer sum modulo two refutes the odd-charge cases. On the even
side a separate algorithm **constructs and checks an original SAT word**.
The experiment never gives the finder a graph, an endpoint map, a charge, a
parity equation, a planted assignment, or original variable names.

## Clause gadget and exact semantic statement

For each ordered proper clause `a OR b OR c` introduce a private start bit
`z`, replace the clause by `a OR b OR z`, and build a strip from `z` to the
**literal** `c`. Each of the `L` intermediate layers has two fresh bits.
Direct implications from the start to both bits in the first layer, all four
implications between each successive pair of layers, and both implications
from the last layer to `c`. Every implication is one binary clause. For
`m` source clauses this adds `m(1+2L)` variables and gives `m(1+4L)`
total clauses in this one-socket encoding.

Any raw model restricts to a core model: if both unchanged literals are
false, the start and then the entire strip must be true, forcing `c`.
Conversely, set **all** auxiliary bits of the strip to the truth value of
`c`. This lifts every core model. The projection is exact, although there
can be additional extensions of the same model. The same signed-literal
substitution sends every binary implication to a tautology and every head
to its original clause. It is part of the construction and proofs, not
metadata available to the finder.

## All small raw integer scopes are blind

Fix any `w<L` and take an arbitrary set of at most `w` coordinates. Impose
all raw clauses contained in this scope (or any subset). At least one whole
two-bit layer is absent in **every** strip. Set the auxiliaries before that
layer true and after it false. No surviving implication crosses the gap,
the start can be true, and the late part does not force an endpoint.
Accordingly, every assignment of the original variables is possible.

More strongly, the integer affine lattice of the scoped models is the whole
integer lattice. For an original coordinate one can flip its value alone
with the preceding auxiliary choices fixed. For an auxiliary coordinate in
a given strip choose source values making its endpoint `c` true and at
least one unchanged head literal true; this is possible because `a,b,c`
have distinct variables. Put predecessors in earlier layers of this strip
false and successors in later layers true. The bit in question can flip
alone; a sibling in the same layer has no edge to it. The other strips use
their gaps as above. These pairs of models give every unit difference, and
there is at least one model. This proves fullness over the integers, so no
nontrivial linear equality or congruence can be obtained from such scopes.
The proof concerns **raw local** laws, not laws about learned clauses,
conditional calls, inequalities, or every integer proof system. We take
`L=16` to exceed the existing integer backend's maximum scope of 15.

For `L>=2`, a start occurs once positively and twice negatively; a first
layer bit has two outgoing links; an internal bit has two incoming and two
outgoing links; a last layer bit has two incoming links. Thus none is a
private pivot with one occurrence in each sign. On the cubic parity family
each core bit has at least two occurrences of each sign, so the old peeler
cannot start. Signed permutations preserve this fact.

## A recognized family with a polynomial decision algorithm

Take any connected finite simple cubic graph and place one Boolean bit on
each edge. Vertex `v` requires the XOR of its three incident bits to equal
its charge. Write the four forbidden words at this vertex as four ternary
clauses; rotate the designated endpoints among positions `0,1,2,0`. In
the one-socket encoding, every edge variable still appears in at least two
distinct raw ternaries at each endpoint vertex. Every auxiliary appears
in at most one ternary. The syntactic anchor rule therefore identifies
exactly the edge variables, independent of literal ordering and sign renaming.

Searching from the start of a head until the first anchor on each branch
finds precisely its intended endpoint literal. The forward implication
graph on this search is just the strip; the reverse-complement implications
do not add a departure from a positive strip helper. Stopping at the first
anchor avoids traversing another gadget in reverse. No raw clause is
anchor-only. Thus the recovered clauses are exactly the original parity CNF
up to the common signed permutation. Each of the `m=4|V|` searches visits
`4L` forward arcs and needs `L+1` binary steps in its saved proof.

For odd total charge the sum of the recovered vertex equations modulo two
has zero coefficient on every edge (two endpoints), while its right-hand
side is one. Complementing an edge toggles two charges, preserving the
total. Each recovered vertex support has exactly one parity half-cube of
allowed local words; checking the resulting integer-law certificate does
not require trusting the story about the graph.

For even total charge the core equations are consistent: fix non-tree
edges arbitrarily and eliminate leaf edges in a spanning tree. The last
vertex equation follows from the even sum. The implementation does not
need to find this tree. The [witness constructor](../src/pnp_lab/feedback_witness.py)
recognizes when the entire recovered CNF consists of exact three-bit
parity blocks, solves them once by elimination over F2, and fixes this
anchor assignment in the **original** clauses. In this family at most one
literal of a ternary head remains unfixed. Everything left is a 2-CNF;
it is satisfiable by the lifting argument. The existing iterative
[strong-component solver](../src/pnp_lab/observation_2sat.py) returns an
extension. The resulting original word is accepted only after evaluating
every raw clause. For background see [Aspvall, Plass and Tarjan
(1979)](https://doi.org/10.1016/0020-0190%2879%2990002-4).

Run the witness constructor first and, if it fails, the feedback refuter.
On this family only the odd side needs refutation, where the direct
weight-one parity sum succeeds. This yields a uniform polynomial-time
decision algorithm on the stated images when the budgets permit the work.
For example, with the canonical dense variable labels (or any signed
permutation of them), write `N` for the explicit input bit length. There
are `O(N)` variables, clauses, arcs and stored path steps. Gaussian
elimination uses `O(N²)` row additions on `O(N)`-bit rows. Residualization,
sorting/indexing, packed-word construction, and replay have polynomial bit
cost: even charging linear bit work for each label/mask operation and
linear dictionary scans in place of constant-time lookup gives a coarse
polynomial bound. Each signed certificate index uses `O(log N)` bits.
The finite default caps are not mathematical completeness guarantees.
At most two discovery passes are needed by this decision order; counting
only the final proof would omit discovery and SAT lifting costs.

For a general input a parity projection can have a solution which does not
lift. Detecting an inconsistent residual under that **one** assignment
returns `UNKNOWN`, not UNSAT. For example, even parity of `x,y,z` together
with the unit `g` and `not g OR x` is satisfiable, but the all-zero parity
assignment cannot lift. The [regression test](../tests/test_feedback_witness.py)
checks this failure as well as the actual satisfying word.

## Two ways the approach stops

**No anchors.** Replace all three literals of each original clause by distinct
fresh starts; attach a separate directed strip from each start to its
corresponding original literal. This three-socket construction has exactly
the same SAT projection: any true start forces its target, and assigning
all strip bits to their target values lifts every original model. Every raw
ternary variable occurs in exactly one ternary. The anchor learner therefore
returns no clauses at all, on both SAT and UNSAT images. Raw local lattice
blindness also persists for `w<L`: use each strip's missing layer to satisfy
its head. To flip a designated auxiliary, choose its endpoint true and leave
the other starts of the same head true using their missing layers.

For fixed `L` this is a linear number of auxiliary variables and clauses
per original proper 3-CNF and a polynomial-size many-one reduction.
Proper three-distinct-literal 3SAT already covers general 3SAT: discard
tautologies and duplicate literals; extend a short proper clause by all sign
choices on enough fresh coordinates to reach width three (an empty clause
uses all eight choices). Satisfiability is unchanged. Hence SAT on the
three-socket images is NP-hard and the restricted decision task is in NP
under the usual image promise. The blind frontend is a property of this
particular rule; it does not make arbitrary preprocessing impossible.

**Every core clause is recovered, but the backend has no law.** Take the
previous [31-variable/152-clause twins](correlation_proof_boundary.md) and
make a one-socket copy for **each** of the three cyclic rotations of every
clause. This forces every original coordinate to appear in start ternaries
at least twice. Copies of the same recovered clause coalesce. In both
finite tests the projected CNF is exactly the 152-clause core under signed
renaming, yet all 152 profiled triple supports emit zero integer laws.
The refuter and the parity-only witness constructor both return `UNKNOWN`.
The UNSAT label is checked independently with the earlier raw refutation
on the core; the positive twin has an actual lifted word. Length two is
enough for this diagnostic: it does not use or claim the raw width-15
blindness theorem. Thus the two negative controls isolate different failures.

## Measurements and reproduction

Each input below is independently presented with signed variable renaming,
literal reorder and clause reorder; the SAT/UNSAT siblings of one size share
the permutation. The oracle compares the recovered clauses with the core
after the same permutation, separately from discovery. K4 and a 12-vertex
prism are finite function tests, not asymptotic expanders.

| One-socket parity case | K4 | 12-vertex prism |
|---|---:|---:|
| Raw variables / clauses | 534 / 1,040 | 1,602 / 3,120 |
| Fully profiled raw integer scopes, per signing | 1,568 | 4,704 |
| Raw integer rows / private elimination steps | 0 / 0 | 0 / 0 |
| Anchors / recovered clauses | 6 / 16 | 18 / 48 |
| Finder arc visits / stored path steps | 1,024 / 272 | 3,072 / 816 |
| Odd side: modulus-two certificate terms | 4 | 12 |
| Odd side: compact certificate bytes | 2,591 | 8,167 |
| Even side: F2 rank / candidate assignments tried | 3 / 1 | 11 / 1 |
| Even side: residual SCC literal vertices / arcs | 1,056 / 2,003 | 3,168 / 6,014 |

Both constructed SAT words differ from their planted controls; each is
checked against **every** original clause. The experiment runs the refuter
and witness constructor separately on each twin to record where each stops,
so the table's finder counts refer to a single discovery pass. On the
three-socket K4 both signs have 1,590 variables, 3,088 clauses and zero
anchors. On the rotated previous core each sign has 2,311 variables and
4,104 raw clauses; every one of the 152 distinct clauses is recovered.

Run `PYTHONPATH=src python experiments/integer_feedback.py --out-dir reproduced`.
The [report](../results/integer_feedback.json) contains statistics, a proof
sample and a constructed SAT word. To replay a sample, regenerate
`feedback_case(graph_vertices, odd_charge, layers=layers)`, apply
`scramble(N, raw, None, seed)`, and run `check_integer_feedback` or
`check_feedback_witness` on the regenerated raw clauses. The recorded SHA-256
is over the compact JSON array in that exact presented order. A digest
identifies the input; it never substitutes for checking a derivation or word.
