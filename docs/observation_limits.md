# Small observation codimension: what is known, and why it need not be small

The [observation solver](../src/pnp_lab/observation_2sat.py) represents each
forbidden affine event of rank at most two with at most two equations. With
one Boolean variable for each of the `K` distinct homogeneous linear forms
appearing in these equations, avoiding the events is a 2-CNF. Equation
right-hand sides become literal signs. The form values must also be the
image of a single parameter point. If the forms have rank `R`, that image
is a subspace of codimension `k=K-R` and can be given by `k` independent
parity checks. One may instead describe an affine coset by shifting signs.
A satisfying observation word lifts by Gaussian elimination; the lifted
assignment is checked on the original events.

## Upper bound and literature

The resulting problem is **2-SUB-SAT**, not a new general complexity class.
Arvind and Guruswami, [*CNF Satisfiability in a Subspace and Related
Problems*, IPEC 2021](https://doi.org/10.4230/LIPIcs.IPEC.2021.5), Theorems
2/17 and 19, give a deterministic algorithm with the binomial subset bound
in the codimension and prove W[1]-hardness in that parameter. They also
relate the subspace problem to avoidance of affine subspaces. See the
[authors' full version, §§2.4 and 3.2](https://arxiv.org/abs/2108.05914).
Earlier, Brakensiek, Gopi and Guruswami studied 2-SAT subject to global
modular conditions via polynomial representations ([paper](https://doi.org/10.1137/19M1291054)).
Another relevant connection is Mastrolilli, [*The Complexity of the Ideal
Membership Problem for Constrained Problems Over the Boolean Domain*](https://arxiv.org/abs/1904.04072),
Theorem 1.2 of the manuscript, on bounded-degree ideal membership including
Boolean majority-closed constraint languages. We do not need to construct
a Gröbner basis, or transfer a theorem between coefficient fields, in the
following direct GF(2) argument. No priority claim is made for the XP bound
or the multicolored-clique reduction.

**Why the implemented closure enumeration suffices.** Find any satisfying
2-CNF assignment by implication graph SCCs; no such assignment already means
UNSAT. Flip the variables by this assignment, so zero satisfies the shifted
2-CNF. Its clauses are now implications, prohibitions of a pair of positive
flips, or prohibitions of a single flip. For any seed set `T`, close under
all implications. If the closure violates a prohibition, no valid superset
exists; otherwise it is the least valid superset `M(T)`.

The product of the `k` parity-check indicators is a Boolean polynomial of
degree at most `k`, and is one exactly on consistent observation words. The
same degree bound holds after the shift. On any valid flip set `S` a
squarefree monomial for seed `T` evaluates to one exactly when `T ⊆ S`,
equivalently `M(T) ⊆ S` for feasible `T`. Discard infeasible seeds and
collect coefficients with identical closures. In increasing size order on
the resulting family of distinct closures, their inclusion matrix has unit
diagonal and is triangular. Thus a polynomial of degree at most `k` that is
zero on all the feasible `M(T)` with `|T|≤k` is zero on every valid flip
set: all its collected coefficients vanish. Conversely a consistent closure
is a directly checkable witness. This proves completeness of the unbounded
run without expanding the product explicitly. The number of attempted
seeds is at most `sum_{j=0}^k binom(K,j)`, with polynomial work per seed
and polynomial space. This is polynomial for each **fixed** `k` (XP), not
a fixed-parameter bound `f(k)·poly(N)` with a universal polynomial exponent.
A capped unfinished run returns UNKNOWN, not an exhausted-closure UNSAT.

## Preserving codimension even after local observation changes

Start with a graph partitioned into `k` nonempty color classes and ask for a
clique choosing one vertex of every color. Empty classes can be handled
immediately. The starting 2-SUB-SAT encoding is exactly the one in
Arvind–Guruswami §3.2: use a bit `y_v` per vertex, forbid selecting two
vertices of one color and forbid incompatible pairs of different colors.
These are negative binary clauses. For each color require odd selection
parity. Since at most one vertex is selected per color, these `k` equations
force exactly one. A solution is precisely the required clique.

The extra argument here accounts for **the choice of local observation
coordinates in the compiled arrangement**. First enlarge each class of size
less than five to size five by cloning alternatives with their original
cross-color neighbors. The predicate remains unchanged after projection to
original alternatives; counts can change. Write `N` for the new total. Give
each class of size `b` independent free bits for `b-1` vertices, and express
its last vertex as `1 + XOR(free bits of this class)`. There are `N-k` free
bits. Turn each forbidden pair `y_v=y_w=1` into a rank-two event on them.
Offsets in this parametrization are incorporated in the right-hand sides.

Let `a_v` be the homogeneous observation normal for vertex `v`. The `N`
labelled normals have rank `N-k`: their full relation space is generated by
the `k` disjoint sums of all normals of a color. Hence no relation involves
four or fewer vertices. All normals are nonzero, distinct, and, for every
forbidden pair, the third nonzero vector of its two-dimensional span is
`a_v+a_w`. This third vector is not any vertex normal and belongs to no
other pair plane: equality with another pair sum would give a relation on
at most four vertices. Consequently each plane can use its two original
normals or replace one of them by its private pair sum.

Suppose a local two-row representation omits `s` original normals globally.
A forbidden pair cannot omit both endpoints; only one other line exists in
its plane. Every omitted vertex has at least four same-color partners. Each
of these pairs must now use its private sum, and no sum is counted twice
because omitted vertices are independent in the forbidden-pair graph. Thus
there are at least `(N-s)+4s` distinct observations. The original normals
attain `K=N` and cover every vertex; the total span is invariant under local
basis changes. Since the implementation includes the original input masks
as a candidate and does not choose a larger union, its observed deficiency
is **exactly `k`**, as is the optimum within this family of local choices.
This statement does not optimize arbitrary global logical reformulations.

This polynomial reduction transfers W[1]-hardness to the presented
rank-two event problem parameterized by that measured deficiency. An
`f(k)·poly(input size)` algorithm would imply FPT=W[1]; this is a conditional
parameterized complexity consequence, not an unconditional lower bound for all
algorithms or a resolution of P versus NP. It does not invoke ETH.

## A connected limitation of the explicit closure algorithm

Take `k≥2` classes of `b≥5` alternatives. Forbid all cross pairs between
the last two classes, so a multicolored clique is impossible. On each pair
of consecutive classes also forbid the pair of their distinguished number-0
alternatives. The forbidden-pair graph is connected, yet the ordinary
2-CNF without parities allows the empty selection and every singleton.
The just-proved optimum implies the solver uses exactly the original vertex
normals (up to ordering); literal offsets just translate these words.

Whatever base 2-CNF model the solver picks, each vertex coordinate can be
flipped in a feasible model, and no two coordinates define identical flip
conditions (test the empty selection and singletons). Hence all `kb` unary
closures are viable and distinct. With no budget, the current combination
loop attempts exactly `sum_{j=1}^k binom(kb,j)` nonempty seeds on these UNSAT
inputs. This is about that loop, not an intrinsic cost of clique detection.

There are even at least `(b-2)^(k-2)` **distinct viable closures** generated
by small seeds. For each of the first `k-2` classes choose a nondistinguished
vertex different from any base selection. Flip it on. Its only conflicts
are within its own color; turning off a previously selected vertex of the
same color is necessary and sufficient. The resulting set of flips is the
least feasible closure of these `k-2` generators. Different choices give
different closures, while the unchanged last two colors still cannot both
meet their parity checks. A smarter procedure could notice the simple
last-two-color obstruction immediately. We do not infer a lower bound for
such procedures or for arbitrary 2-SUB-SAT algorithms.

The [experiment](../experiments/observation_2sat.py) checks raw parameter
assignments, projects SAT witnesses to original graph vertices, and compares
against independent clique enumeration on the original graph. At `b=5`,
`k=2,3,4` the UNSAT runs tried 55, 575, and 6,195 nonempty seeds, with
11, 65, and 380 distinct viable closures tested including the base. A
planted clique on original classes of sizes `(2,3,2)` is recovered after
cloning to `(5,5,5)`. The [report](../results/observation_2sat.json) labels
these as finite checks and exposes the work-limit control separately.
