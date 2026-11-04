# Recovering the old blind encoding from its signed clauses

**Result.** A polynomial preprocessing pass, without generator-supplied tags,
copy correspondence, variable names or sign orientation, recognizes enough
structure to undo the [simple-support reduction](split_parity.md). For any
proper three-literal-per-clause source (distinct variables in each clause),
it recovers exactly the set of source clauses up to variable renaming and
complementation, dropping unused variables and duplicate clauses. It also
works after arbitrary permutations of the variables, clauses and literals
and independent complementations of variables in the encoded input. With
short source clauses the pass can simplify further; its guarantee there is
satisfiability equivalence and lifting, not recovery of identical syntax.

This identifies an explicit padding that can be removed before using a
solver. The recovered problem on arbitrary source formulas is still
NP-complete. The pass does not produce a polynomial-time general SAT decider.

## Finding a certified local consequence

Form the closed neighborhood of each variable in the primal graph: the
variable together with all variables co-occurring with it in an input clause.
For neighborhoods with exactly six variables, inspect the proper ternary
clauses supported wholly inside. Count *distinct supports*. Keep the candidate
if all six coordinates occur in at least two internal supports, and at least
five coordinates each occur in at least four. This is purely a candidate
filter; none of these graph statistics proves that a literal is forced.

The [implementation](../src/pnp_lab/blind_recovery.py) enumerates all 64
words on each retained scope. If every word falsifies a selected clause, the
whole CNF is UNSAT. Otherwise all bits constant across the local satisfying
words are forced by those original clauses. Store only the scope and input
clause indices for proof replay. Multiple distinct packs may be found on a
general input; opposing certified pins imply UNSAT. The filter is neither
a complete solver for six-variable sources hidden anywhere nor a complete
enumerator of every small implication.

**Why it finds precisely the right pack on the old image.** For this paragraph
only, use the constructor's names to describe the proof. Gadget variable 3
co-occurs with all five other gadget bits and never with an external bit.
Thus its closed neighborhood is precisely the gadget. The ten gadget clauses
have ten distinct triple supports; their internal degrees are 5,5,7,5,6,2.
The local satisfying words are 62 and 63 (bit 1 has weight 1), so bits
2 through 6 are forced true. An actual empty source clause reinstates the
eleventh clause, making the local table empty. Sign flips and reordering
preserve the argument.

Conversely, each occurrence copy appears in at most three clauses, and the
two extra filler variables in just one. Therefore at least five gadget bits
are needed for any qualifying six-bit pool. If its sixth variable were an
outsider, it would need to appear at least twice in clauses with two gadget
bits. Each outside copy can do so at most once (its own padded unit clause),
and a filler cannot. Thus no spurious pack is selected; the source itself is
not assumed to obey any degree bound.

## Contracting the binary equations with an independently replayable certificate

Substitute the forced bits. For every remaining binary clause
`(a OR b)`, add implications `not a -> b` and `not b -> a`; a unit is a
duplicated bit for this purpose. Keep the original clause index on each
edge. Each signed literal in a strongly connected component has the same
truth value. A component containing both signs of a coordinate certifies
UNSAT. Otherwise identify its signs with a representative and use the
opposite signs in its complementary component. This is the classical
implication-graph principle; see Aspvall, Plass and Tarjan,
[*A linear-time algorithm for testing the truth of certain quantified
Boolean formulas*](https://doi.org/10.1016/0020-0190(79)90002-4) (1979).
There is no novelty claim for this principle.

For each nontrivial represented component, record a directed tree out of the
representative and a reverse tree back to it. The independent checker
does **not** run the graph search, require maximality, or trust an assertion
about reachability. For each parent/child edge it checks against the named
source clause after the certified local pins, then checks that both trees
reach the same signed vertices. That suffices for all substitutions. It
reconstructs the residual by substitution, removing tautologies and
duplicates, satisfying any isolated single binary clause on two private
coordinates, and packing used variable names. All recorded final clause and
variable images must match the reconstruction (a Boolean constant is not
the integer variable ID 1). A model of the reduced formula lifts by evaluating
these images; `lift_recovered_model` verifies the full user CNF on the lifted
word. In the forward direction a model of the original agrees with all pins
and component identifications; changing a private isolated binary component
to the chosen fixed model cannot affect another clause.

After the gadget pins are set, a proper source formula leaves precisely its
occurrence triples, directed binary cycles on copies of each used source
variable, and an isolated filler disjunction. The cycles for distinct
source variables do not share vertices, and the filler does not imply any
equivalence. Contracting each cycle and dropping the filler proves the
exact recovery theorem above. For short source clauses, their own binary
implications can merge more coordinates, soundly.

**Cost.** There are at most n candidate neighborhoods. Build an index of
input triples; look up at most 20 supports per six-bit neighborhood and
evaluate at most 64 local words. Even if a raw clause is inspected in every
candidate pack this is polynomial in explicit input length. The binary
graph and its two trees per component have linear total graph size.
Sorting/deduplication and constructing/checking compact integer masks are
also charged at polynomial bit cost. Enumerating satisfying words for the
recovered global formula is not part of this bound.

## Results, limits, and reproduction

[The replay experiment](../experiments/blind_recovery.py) scrambled
coordinates, signs and row order. In 48 small proper signed 3-CNFs it
checked exact recovery under the induced coordinate bijection and compared
2,288 original assignments. The comparison oracle uses the constructor's
correspondence; the recovery procedure never receives it.
On the odd-charge 128-switch example the old image has 12,932 variables and
18,113 clauses. Its raw one-split parity extractor generates no row. The
new replayer checks a single six-bit local table and 24,050 tree-edge
justifications, yielding 899 variables and 2,568 clauses. The existing
split-parity solver produces a checked refutation of that smaller formula.
On the even-charge sibling it produces no contradiction; the experiment
projects a known model, lifts it through the verified map and tests all
18,113 original clauses. These are actually executed sizes.

**An NP-complete representation where this pass does nothing.** Take any old
image and, for each of its six gadget coordinates v, add two clauses
`(v OR p OR q)`, each with entirely fresh p,q. Every old model extends;
on the other hand every new model restricts to an old one. All supports
are still distinct and ternary. Every one of the six gadget variables now
has more than six variables in its closed neighborhood. No outsider can
be the center of the exact gadget scope. No other dense six-bit pack can
qualify either: outsiders still have degree at most three and occur in at
most one clause with two gadget bits. Therefore there are zero selected
packs, no binary contractions and no isolated binary clauses to delete.
The output on this extended image is unchanged up to ordering and packing.
The original root single-pass parity filter is also silent, since all triples
are proper and unique. This obstruction concerns the stated filters.
For example an unrestricted search through all six-element sets could
recover the original gadget despite the added clauses; that would not
prove all other SAT instances easy.

[Report](../results/blind_recovery.json) · [tamper tests and exact small
comparisons](../tests/test_blind_recovery.py). From the repository root:

```bash
PYTHONPATH=src python experiments/blind_recovery.py --out-dir reproduced
```
