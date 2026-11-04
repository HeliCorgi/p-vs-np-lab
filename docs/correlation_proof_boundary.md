# What retaining nonlinear correlations buys, and where the bound stops

The previous integer-affine relaxation loses information needed on the signed
31-variable, 152-clause fixture. Keeping that information now gives a checked
refutation and exact finite thresholds in several familiar proof systems:

| Measure on the original UNSAT fixture | Exact minimum | Lower-bound reason | Upper-bound evidence |
| --- | ---: | --- | --- |
| Ordinary resolution clause width | 4 | Every first nontrivial resolvent has width 4 | Checked 368-line DAG |
| Largest union of variables in exact join/project reasoning | 5 | Union at most 4 cannot combine distinct clause cylinders | Checked translation of the resolution DAG |
| Polynomial-calculus degree, over any field | 5 | Degree-four invariant for proper linear triples | Direct translation of the same DAG |
| Local-distribution Sherali–Adams level, in the convention below | 5 | Explicit feasible level-four marginals | Union-five refutation rules out level-five marginals |

These are different measures; their numbers should not be interchanged.
The executable polynomial checker uses F2. The all-field degree statement is
the mathematical argument below. The Sherali–Adams result uses explicit
rational distributions and a proof of the level-five obstruction, with no
LP solver execution. None of these facts resolves P versus NP or establishes
a new proof system. No novelty is claimed for the elementary comparisons.

The input is obtained by `n, raw = line_fixture(0)` and `clauses = raw[:152]` from
[the raw modular barrier](modular_barrier.md). Every clause has three distinct
variables; any two unsigned supports intersect in at most one variable.
The pairwise condition is on distinct raw clauses, so there is at most one
clause per unsigned triple, even if its signs would differ.
Here “linear” describes this hypergraph property, not linear equations. The
same supports with all-positive literals are satisfiable. Selecting the
supports using F2 does not turn their OR clauses into parity constraints.

## 1. Exact relations are an established proof language

For a relation `R` on a set `S` of Boolean variables, each forbidden tuple
`a` supplies its blocking clause: the disjunction of literals false exactly
at `a`. The conjunction of these clauses represents `R` exactly. An exact
join intersects lifted relations on the union of their scopes. Projection
existentially eliminates the forgotten variables. These operations preserve
all joint Boolean information on their scopes, including nonlinear
correlations that an affine hull discards.

**Bounded-union simulation.** Suppose every input and intermediate operation
uses at most `K` original variables, including the entire union before a
projection. Then a join/project refutation has an ordinary-resolution
simulation of width at most `K`, allowing weakening. For each forbidden
output tuple, fix that tuple and branch over the variables being eliminated.
Every complete extension violates a parent blocking clause. Weaken that
clause to the full extension's blocking clause, then resolve up the binary
tree. This derives the output blocking clause using only variables in the
union. Summed over all forbidden output tuples, a binary join/projection
step costs at most `O(poly(K) 2^K)` such lines and literal operations.

Conversely, resolving `(x OR A)` with `(NOT x OR B)` to obtain `A OR B`
can be done by joining their exact relations and projecting `x`. If all
resolution clauses have width at most `w`, the union in this simulation has
size at most `w+1`: it contains the resolvent's variables and its pivot.
This proves the upper bound five in the table, rather than four.

The union bound is essential. A small output separator does not charge the
work of computing it from a much larger union. Neither an uncharged
existential projection oracle nor a fresh variable encoding a large relation
is included in this simulation. The connection between consistency and
resolution is established literature; the
[Atserias–Dalmau characterization](https://www.cs.upc.edu/~atserias/papers/width/submitted.pdf)
expresses resolution width `k` through an existential `(k+1)`-pebble game.
The explicit simulation here fixes the resource convention used in this
repository.

### Why the finite union threshold is exactly five

On any proper linear 3-CNF, every relation derivable with union at most four
is either a full cube or a cylinder of one original clause. A clause
cylinder retains that clause on its three variables and leaves all other
scope coordinates free. Projecting out a clause variable gives a full cube;
retaining all three preserves the cylinder. Two different clause cylinders
cannot be joined within four variables, since their supports have union
size at least five. Joining repeated copies of the same cylinder changes
nothing. Induction proves the invariant, so an empty relation cannot occur.

This statement allows raw-clause and full-cube inputs, exact joins and
projections. It does not allow assumption/pinning nodes, arbitrary derived
constraints as new axioms, integer lemmas, or extension variables. On the
specific UNSAT fixture, the checked union-five proof supplies the matching
upper bound; see the
[relation checker](../src/pnp_lab/relation_proof.py).

### A small proof can still have a larger search cost

The [resolution experiment](correlation_resolution.md) independently checks
the width-three fixed point and the width-four refutation. The latter uses
115 original clauses and 253 resolution steps. Its discovery stored 26,826
clauses, checked 180,420 candidate pairs, and performed 463,497 subsumption
subset probes plus 8,085,954 superset containment checks. Pair visits are not
the total work. These discovery costs cannot be replaced by the 368 retained proof
lines when discussing an algorithm's runtime. The old 957-node decision tree
converts to a width-nine, 472-line resolution proof; the new search did not
read that tree.

Global learning also explains why this does not contradict the earlier
local-hull blindness. The first retained binary clause has 13 raw ancestors;
the first retained unit has 41. A small current clause can encode information
that has passed through many raw clauses. Raw-fragment locality and derived
clause width measure different things.

## 2. Polynomial lifting: static span and dynamic calculus differ

Over a field `F`, write `false(x)=1-x`, `false(NOT x)=x`, and encode a clause
`C` by the equation

\[
 f_C=\prod_{\ell\in C}\operatorname{false}(\ell)=0.
\]

Polynomial calculus permits linear combinations and multiplication of a
previously derived polynomial by a variable, with Boolean axioms. Its degree
charges intermediate lines, not only the final constant `1`. A static span
of input-clause monomial multiples is not automatically a complete dynamic
degree-bounded search. The existing
[static backend](overlap_refutation.md) must not be advertised as one.

For this class, however, there is a direct dynamic degree-four obstruction.
In the Boolean quotient `x_i²=x_i`, let

\[
 V_4=\operatorname{span}\{f_C,\ x_jf_C:
                         j\notin\operatorname{vars}(C)\}.
\]

Every cubic leading support is unique. Every quartic leading support is
also unique: two distinct triples in a four-set would intersect in at least
two variables. Hence these generators are independent, and `V_4` contains
no nonzero polynomial of degree at most two. Its dimension on the fixture
is `152 (31-2)=4408`.

For closure under admissible multiplication by `x_i`, a quartic support
missing `i` would create a quintic support. The map adjoining `i` to such
quartic supports is injective, so these quintic terms cannot cancel each
other. A product whose reduced degree stays at most four therefore has no
such quartic terms. For the remaining quartic generators, `i` is either the
extra variable, which fixes the generator, or a clause variable; in the
latter case `x_i f_C` is either `f_C` or zero in the quotient. Multiplication
of the cubic part stays in `V_4`. This proves invariance under every dynamic
degree-four step, even if degree is measured after Boolean reduction.
Thus this stronger quotient calculus cannot derive `1`. An ordinary PC
degree-four derivation maps into it without increasing degree, so it too is
impossible. The argument is independent of characteristic.

For the upper bound, one resolution step with non-tautological resolvent
`R=A union B` has the identity

\[
 ((1-x)f_A)f_{B\setminus A}+(xf_B)f_{A\setminus B}=f_R.
\]

Only missing false-literal factors are multiplied in; shared factors are
not squared. Each multiplier introduces a new variable, so every formal
intermediate polynomial has degree at most `|R|+1`. Multiplication by
`1-y` is implemented by subtracting `y` times the current polynomial.
This works over every field and needs no Boolean reduction in these
translated steps. The width-four proof therefore yields ordinary degree
five. The `+1` convention is also stated explicitly in
[Galesi–Kołodziejczyk–Thapen (2025), page 3](https://theoryofcomputing.org/articles/v021a006/v021a006.pdf).

The [polynomial experiment](correlation_polynomial.md) checks the F2
arithmetic DAG against original clauses: 1,262 nodes, degree five, 6,313
monomial occurrences and at most 32 monomials in one polynomial. The checker
does not invoke the resolution search. A degree cap rejecting a certificate
is not a satisfiability result.

## 3. Nonnegative local distributions: an exact SA convention

Use the CSP form of level `t`: for every variable set `S` with `|S|≤t`, a
nonnegative distribution `mu_S` is normalized, agrees under projection with
every smaller distribution, and gives zero mass to assignments violating an
original clause on its scope. This is the explicit local-distribution
formulation in
[Ghazi–Lee, Section 2](https://people.csail.mit.edu/badih/papers/coding_gaps_arx.pdf).
Some inequality-based hierarchy conventions shift the level number. Our
numeric threshold uses precisely this formulation.

For **every proper linear 3-CNF**, construct feasible level-four marginals
as follows. A scope of at most four variables contains at most one original
triple. If it contains none, use the uniform distribution. If it contains
clause `C`, let `b_C` be its unique falsifying triple assignment and use the
uniform distribution subject to

\[
 \bigoplus_{i\in\operatorname{vars}(C)}x_i
       =1\mathbin{\oplus}\bigoplus_i(b_C)_i.
\]

This half-cube satisfies `C`; any extra coordinate is independent and
uniform. Every proper marginal of the three-variable parity distribution
is uniform. Therefore a projection retaining the triple preserves its
chosen half-cube, and every other projection is uniform. All distributions
agree. The construction supplies a feasible relaxation even when the
original formula is UNSAT. It does not assert that the raw clauses imply
the selected parity equations.

The [compact witness and independent verifier](../src/pnp_lab/local_marginals.py)
store one parity bit per raw clause, then check every table with integer
numerators and denominators. On **each** 31-variable twin the
[experiment](../experiments/correlation_marginals.py) checks 36,457 scopes,
541,323 table cells, 506,667 positive cells, and 1,062,711 one-coordinate
marginal equalities. Single-coordinate consistency composes to every
projection. The output decision remains `UNKNOWN`; only the relaxation is
marked `FEASIBLE`. Unsupported overlaps and exhausted verification budgets
yield no feasibility certificate.

Conversely, if level-`t` local distributions exist, any exact join/project
proof whose union size is at most `t` preserves their support. At a join,
an assignment with positive mass has positive-mass restrictions in both
parents, hence belongs to both retained relations. At a projection, a
positive-mass output assignment has at least one positive-mass extension,
by nonnegativity and marginal consistency. The empty relation would
contradict normalization. The checked union-five refutation therefore rules
out level-five distributions. Together with the explicit level-four
witness, this gives the table's exact threshold.

This uses nonnegative rational masses and all intersection marginals.
The previous integer-affine relaxation allowed signed integer weights and
matched only unary coordinates. These interfaces must not be identified.
Nor does feasibility of every local table alone supply consistent weights.

## 4. A scalable control in the same proper linear 3-CNF class

The small degree-five success cannot justify a fixed-degree all-input
solver. A standard published lower bound already supplies a strong check.
For a set `U` of clauses, let `N(U)` be its incident variables and
`partial(U)` the variables occurring in exactly one selected clause.
[Mikša–Nordström (CCC 2015), Theorem 4.2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol033-ccc2015/LIPIcs.CCC.2015.467/LIPIcs.CCC.2015.467.pdf),
restating Alekhnovich–Razborov, says that

\[
 |\partial(U)|\ge\delta|U|\quad(0<|U|\le s)
       \quad\Longrightarrow\quad D_{\rm PC}(F)>\delta s/2.
\]

It holds over every field for the ordinary raw clause-polynomial encoding,
with Boolean reduction allowed. Their Theorem 2.2 gives the corresponding
PC/PCR monomial-size bound
`exp(Omega((D-width(F))²/n))`. Merely knowing `|N(U)|≥|U|+2` from the old
Hall argument is insufficient for this theorem: a proportional **unique
neighbor** bound is required.

Here is a complete elementary support construction to meet that condition
while retaining proper linear triples. This is a synthesis using the
published theorem, not a claimed new lower-bound result or an implemented
large-instance generator.

1. On `n` variables include each distinct triple independently with
   probability `96/n²`. There are at least `15n` selected triples with
   probability tending to one: the mean is asymptotic to `16n`, and the
   variance is `O(n)`.
2. Put `alpha=7/4`, `epsilon=10^-16`, and `s=floor(epsilon n)`. For a fixed
   number `t` of selected triples, the probability that some such set uses
   at most `floor(alpha t)` variables is bounded by

   \[
   {n\choose\lfloor\alpha t\rfloor}
   {{\lfloor\alpha t\rfloor\choose3}\choose t}(96/n^2)^t
       \le [K(t/n)^{1/4}]^t,
   \qquad
   K=(e/\alpha)^\alpha(e96\alpha^3/6)<504.
   \]

   The cases `t=1,2` are impossible. For `3≤t≤sqrt(n)`, the sum is at most
   the geometric tail starting at power three with base `K n^-1/8`, which
   tends to zero. For `sqrt(n)<t≤epsilon n`, the base is at most
   `K epsilon^(1/4)<0.051`, so this tail also tends to zero. Thus every
   selected `U` with `1≤|U|≤s` has `|N(U)|>7|U|/4`.
3. The expected number of pairs of selected distinct triples sharing two
   variables is
   `binom(n,2) binom(n-2,2) (96/n²)²≤2304`. With probability tending to
   one there are at most `sqrt(n)` such pairs. Delete one triple from each
   original bad pair. This removes at most `sqrt(n)` triples and cannot
   create a new bad pair. Retain exactly `12n` remaining triples for all
   sufficiently large `n`. Every previously established expansion property
   survives deletion of whole clauses, since each remaining subset already
   was a subset of the original sample.
4. Give these supports independent uniform literal signs. The expected
   number of global satisfying assignments is
   `2^n (7/8)^(12n)<1`, so an UNSAT signing exists. All-positive signs on
   the very same supports give a SAT sibling.

For `t=|U|`, write `b=|partial(U)|`. Counting its `3t` incidences gives
`3t≥b+2(|N(U)|-b)`, so `b≥2|N(U)|-3t>t/2`. The raw incidence graph is
therefore an `(s,1/2)` boundary expander. The cited theorem yields

\[
 D_{\rm PC}(F_n)>\lfloor\epsilon n\rfloor/4=\Omega(n)
 \quad\hbox{over every field},
 \qquad S_{\rm PC/PCR}(F_n)=\exp(\Omega(n)).
\]

One support family works for all characteristics; no transfer of a
mod-two Tseitin bound to F2 is being assumed. The resolution-to-PC
simulation also forces resolution width `Omega(n)`. The ordinary
[Ben-Sasson–Wigderson size/width theorem](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf)
then gives exponential resolution length. The bounded-union simulation
forces union size `Omega(n)` for exact raw join/project refutations as well.

This family also passes the previous *starting* integer-blindness control.
For `t≥3`, its expansion implies `|N(U)|≥t+2`; sizes one and two follow
from properness and linearity. The Hall flip-pair argument in
[the integer theory](global_integer_theory.md) therefore applies to every
raw fragment of at most `s` clauses. A variable scope of at most `s`
cannot contain `s` clauses, since any such selection would already use more
than `s` variables. Hence induced scopes have the same guarantee. Count a
pinned variable in the original scope when applying singleton conditioning.

The constants are deliberately loose, and the family is existential.
These claims are asymptotic mathematical bounds, not measurements on the
31-variable fixture, a practical generator, or an NP-hardness reduction
with linear locality. The SAT and UNSAT siblings have different raw signs;
they are not indistinguishable to arbitrary algorithms.

Adding nonnegative consistency is also an established avenue with known
limitations. [Schoenebeck (FOCS 2008)](https://schoeneb.people.si.umich.edu/papers/LasserreNew.pdf)
gives random k-CSP families, including k-SAT for `k≥3`, surviving a linear
number of Lasserre levels; the corresponding weaker SA relaxations survive
as well. This is a separate published family result. We have not proved
that the particular support construction above has that stronger SDP
property, nor transferred it through an unspecified encoding.

## 5. The precise next boundary

The finite gate has been passed: nonlinear information learned from many
raw clauses can separate the old blind twins. Repeating this with a larger
width or degree cap is not, by itself, a new route to a polynomial SAT
algorithm. Full fixed-width closure has `n^O(w)` candidate clauses, and
degree lifting has `n^O(d)` monomial coordinates; the hard family above
requires these parameters to grow linearly for the stated systems.

A concrete next gate is **feedback between checked nonlinear consequences
and the existing global integer solver**. Learn clauses with explicit raw
proofs, recompute selected local relations using them, and retain the
integer proof when those new relations contradict globally. The useful
question is whether this feedback has a family-wide advantage over either
stage alone. The newly constructed family is a meaningful control because
it defeats both the starting raw integer interface and bounded-degree PC.
It is not yet a lower bound on the feedback combination.

Before accepting such a result, specify every hybrid inference rule and
charge the whole proof and search: learned clauses, local table cells,
integer coefficient bit lengths, and any branches. Demonstrate a positive
theorem on an infinite family and compare against the appropriate existing
proof systems. For a P=NP conclusion, the missing obligation is still a
uniform polynomial total bound and complete correctness on **every**
3SAT input, as stated in [the solution criteria](solution_criteria.md).
A restricted proof-system lower bound cannot supply a P≠NP conclusion.

Fresh extension variables need the same precision. Giving a name to a
nonlinear function can reduce visible scope while moving information into
its definition. Include the defining constraints, their derivations and
the cost of expanding or otherwise reasoning about them. Complement
variables in PCR have specified degree-preserving definitions; arbitrary
extension variables do not automatically inherit ordinary resolution or
PC lower bounds. Likewise, an integer-lemma node is not an ordinary
resolution node. The earlier [resolution barrier](layered_resolution_barrier.md)
applies to the stated resolution-justified substitutions, and cannot be
silently promoted to a theorem about this proposed hybrid.
