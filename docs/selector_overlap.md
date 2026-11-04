# Four affine covers of a signed 3-CNF

Can the holes left over by [punctured-flat merging](hole_flats.md) be handled
jointly? We first write the earlier hard case in coordinates where its holes
are explicit. Then we reduce the number of coordinates and forbidden flats.
On the old eight-clause UNSAT cube, the change lowers the minimum static
certificate degree from four to three. The [fully reproducible experiment](../experiments/selector_overlap.py)
produces both a refutation and, on the original representation, a certificate
that the smaller degree cannot work. These are encoding and proof-system
results, not a claim that a fixed degree decides general SAT.

In this note `+` is XOR. A forbidden event is the conjunction of some affine
equations over GF(2) and represents the points where **all** its equations
hold. We seek a point outside every event. A nonempty flat of rank two has
one quarter of the ambient points. If all nontrivial events have rank one,
this decision problem is polynomial: avoiding one hyperplane is a single
opposite affine equation, and all opposite equations are solved together by
Gaussian elimination. An empty event set as a subset of the space forbids
nothing; an empty *list of equations* is the whole space and forbids everything.
Rank two already suffices to express every 3SAT instance, as follows.

## Coordinate conventions and witness contract

Let `n` be the size of the supplied variable scope (including unused bits),
`m` the clause count, and `f_i` the falsity bit of a literal: `1+x` for `x`,
`x` for `not x`. Each nonempty clause has at most three occurrences; pad a
short clause by repeating its last signed literal to obtain three positions.
An empty clause contributes a whole-space event. Padding preserves truth
but repeated literal **positions** are different witness choices. Private
auxiliary bits are never shared by two clauses. The converters validate the
complete input even if an empty clause is present.

| Construction | Private bits per clause | Rank-two events per nonempty clause | Extensions of a satisfying source assignment, per clause |
|---|---:|---:|---|
| Strict selector | 2 | 4 | `t`, the number of true padded positions |
| Odd selector | 2 | 3 | `2^(t-1)` |
| Compact decision gadget | 1 | 2 | 2 if literals 1 and 2 are both true; otherwise 1 |
| Parsimonious gadget | 1 | 3 | exactly 1 |

Every false clause allows zero extensions in all four versions. Multiply the
per-clause extension counts for a fixed source assignment, then sum over
source assignments to get the number of parameter survivors. Only the last
construction guarantees equality to the number of source models in general.
All the constructions have polynomial **bit** size: the modest number of
rows is not treated as permission to store or operate on arbitrarily wide
masks at constant cost.

## 1. Old hole system, with the coordinates made explicit

For each clause introduce `u,v` and define the three selection bits
`b_1=u, b_2=v, b_3=1+u+v`. These are exactly the four odd-parity triples.
Forbid `(b_i=1, f_i=1)` for every occurrence. For strict selectors also
forbid `(u=1,v=1)`, excluding `111` and leaving the three one-hot choices.
A surviving assignment thus picks at least one true occurrence per clause.
A source model extends by picking exactly one true occurrence, also when
`111` is permitted. With `t>0` true positions, there are `t` one-hot choices
and `2^(t-1)` odd subsets of these positions. This proves the first two rows
of the table, including signed literals and repeats.

On the exact-width, repeated-variable-occurrence class in the previous
[no-merge theorem](hole_flats.md), the relaxed bridge's decompositions are
already parametrized by `n` source bits and these `2m` selector bits. Its
initial binary-copy absorption fixes the copies uniquely; the four local
missing points per clause are precisely the four bad events above. For
other input shapes this file supplies its own SAT-preserving reduction;
it does not assert that every previous solver run uses the same basis or
has the same intermediate decomposition count.

## 2. One private bit is enough

For the **compact decision** construction, the two events for a clause are

```
E1: f1=1 AND z=0
E2: f2=1 AND z=f3
```

Here `z=f3` is just one affine equation even when literal 3 is positive.
When both gates fire, the forbidden `z` values are `0` and `f3`;
these cover both values exactly if `f3=1`. If at most one gate fires,
at least one bit survives. Thus projection onto the source bits excludes
exactly the original clause's false assignments. Both auxiliary values
survive exactly if neither gate fires. A deterministic lift is
`z=1+(1+f1)f3`; it always satisfies both exclusions when `f1 f2 f3=0`.
Each first equation has weight one, and the second equation in each pair
has weight at most two. Every nonempty-clause event has rank exactly two,
since its private `z` occurs in only the second row.

To preserve **counts**, instead exclude the following three events:

```
A: f1=0 AND z=1
B: f1=1 AND z!=f2
C: z=1 AND f3=1
```

The first two force `z=f1*f2` for every source assignment; the final event
then excludes exactly `f1*f2*f3=1`. The lift is unique even when several
literals are true. This is a parsimonious reduction from counting the
models of the original signed 3-CNF to counting survivors of sparse affine
rank-two holes. It does not use a model count from the earlier width-three
bridge that had multiple extensions.

**Local sharpness.** Consider a single OR on three *distinct* variables,
with its three source coordinates retained, unrestricted independent Boolean
auxiliaries, and only a union of forbidden affine flats of codimension at
most two. There are no side constraints, including constraints imported from
neighboring gadgets. With no auxiliaries a nonempty such flat on three bits
contains at least two points, so a union of them cannot exclude exactly the
single false point. With arbitrary auxiliaries a single flat cannot do it
either: to reject that false point it must contain its whole auxiliary
fiber. Its direction space then contains the full auxiliary subspace, so
it is a cylinder over a source flat of codimension at most two, again
rejecting too many source points. One auxiliary and two events are sufficient
and minimal under these assumptions for existential decision.

For a parsimonious gadget the total number of survivors must be exactly
seven. For `N≥5` total bits, each of two rank-at-most-two flats has even
size, and their intersection is empty or has dimension at least `N-4`,
again of even size. Inclusion-exclusion leaves an even number of survivors.
For `N=4`, their union would need size nine. Ignoring empty/whole flats,
their sizes are 4 or 8: two 4s cannot reach nine, `4+8` would require an
intersection of size 3, and `8+8` one of size 7, both impossible. The
`N=3` case was already excluded. Hence two such events cannot preserve the
count, no matter how many private auxiliary bits are permitted. The one-bit,
three-event construction attains the bound. These local results do not
exclude global encodings that share bits or constraints, eliminate source
coordinates, or use other forbidden relations.

## 3. How the encoding changes the certificate degree

Work in the Boolean polynomial ring over GF(2), reducing `x_i^2=x_i`.
The indicator of a forbidden conjunction is the product of its equation
indicators. A [static certificate](overlap_refutation.md) is an identity
`1 = sum m_i I_i` with squarefree monomial multipliers (possibly many terms
per event). It proves UNSAT because all `I_i` vanish on any avoiding point.
A term is charged `rank(event i)+weight(m_i)`. All degree statements here
use this *static* convention, not merely the simplified output degree of a
product and not a general lower bound against algorithms or dynamic proofs.

For the selector encodings `I_i=b_i f_i` and the extra strict indicator is
`uv`. The false-clause indicator `L=f1*f2*f3` obeys

```
L = (f2*f3) I1 + (f1*f3) I2 + (f1*f2) I3,
```

since `b1+b2+b3=1`. Expand the affine falsity factors in each multiplier
into monomials before passing a certificate to the checker. The `uv` event
is unnecessary in this derivation. In the compact version,

```
I1 = f1*(1+z); I2 = f2*(1+z+f3); L = f2*I1 + f1*I2.
```

In the parsimonious version the first two indicators sum to `z+f1*f2`;
with the last indicator `z*f3` this gives `L=f3*(I_A+I_B)+I_C`.
Thus a source static refutation using **distinct width-three** clause
falsity indicators lifts with degree overhead at most one in the strict/odd
system and no increase in the one-bit systems. This follows termwise:
a source monomial of weight `s` times a cubic costs `s+3`, and the lifted
multipliers have weights at most `s+2` or `s+1`, respectively. The conclusion
is a simulation on normalized width-three inputs, not a statement that a
general proof can be found quickly. The cubic identities themselves remain
true with repeated/padded literals.

There are useful reverse substitutions valid even on nonsatisfying source
assignments. In strict/odd use `u=1+f1, v=f1*(1+f2)`; the first two bad
indicators and `uv` become zero, and the third becomes `L`. In compact use
`z=1+(1+f1)f3`: `I1` vanishes and `I2` becomes `L`. In parsimonious use
`z=f1*f2`; both gate errors vanish and the remaining bad indicator becomes
`L`. A selector certificate of charged degree `D` can therefore be turned
into a source refutation of degree at most `2(D-2)+3=2D-1` (for genuine
width-three clauses): each multiplier had weight at most `D-2`, and the
substitutions have degree at most two. This bound concerns degree and need
not preserve proof size. See the [separate lower-bound discussion](overlap_refutation.md)
for the distinction between static proofs, polynomial calculus, and SAT.

## 4. The previously unresolved cube: upper *and* lower witnesses

Use all eight signings of `(x,y,z)` as separate clauses. Each source point
falsifies exactly one clause, so `sum_C L_C = 1` as a Boolean polynomial
identity. Substituting the preceding local identities proves that the
forbidden flats cover all parameter points. The [report](../results/selector_overlap.json)
stores the actual event/multiplier labels in every explicit refutation;
`verify_cover_certificate` expands the supplied equations and checks the
constant identity. On the strict representation this is a 54-term proof
(432 bytes of compact certificate JSON, excluding the instance); the same
proof idea works with the fourth event omitted.

Can degree three suffice on the strict cube? Its 32 events each have rank
two, so the only permitted multipliers are 1 and the 19 parameter bits.
There are 640 allowed rows in a space of 1,160 degree-at-most-three squarefree
monomials. The experiment supplies a dual certificate: a linear functional
on those monomials over GF(2), specified by just 59 monomial masks where
its value is one. The independent check sees `functional(1)=1` but
`functional(m I_i)=0` for **every** allowed row. No linear combination of
them can equal 1. Rechecking the 480 available rows after omitting the eight
selector events proves the same negative result. Coupled with the explicit
degree-four proof, the minimum degree on this instance is exactly four.
The lower bound follows from the recorded dual functional, not from an
unsuccessful solver run or elapsed time.

On the compact cube there are 11 bits and 16 rank-two events. The cubic
identity gives a 24-term degree-three proof. No degree-two proof is possible:
multipliers would all be scalars. For a clause with coefficients `a,b`, the
coefficient of its private `z` in that hypothetical identity is `a f1+b f2`.
It must vanish identically. Distinct variable positions force `a=b=0` for
every clause, leaving zero, not one. For the parsimonious cube with 24 events,
the corresponding coefficient is `a(1+f1)+b f1+c f3`; independence of
`1,f1,f3` forces all three scalars to zero. The explicit degree-three proof
there has 32 terms. Hence both one-bit versions have minimum static degree
three on this example. The generic bounded search also finds checked proofs.

Removing the final `(+++)` clause gives the unique source model `000`. The
numbers of surviving parameter assignments are respectively **24, 32, 4 and
1** for strict, odd-only, compact and parsimonious. Each witness decoded by
the [production converters](../src/pnp_lab/selector_events.py) is checked
against the original signed clauses. The exact overlap counter in this
experiment explicitly conditions on **all three source bits** (eight slices);
that reference calculation is not a polynomial-time strategy for unbounded
`n`. Forty additional small formulas and controls include units, empty clauses,
repetitions, signs, tautologies, unused variables and the empty conjunction.
Across all four modes they test each source fiber's size by direct enumeration
(12,552 parameter assignments). These controls test the implementation;
the all-input claims above are algebraic arguments.
