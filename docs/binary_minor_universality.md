# Every binary column matroid occurs as a minor after affine absorption

**Question.** Could the sparse 3SAT encoding force the difference vectors of
its remaining supports into some tractable minor-closed binary matroid class?
Even applying the lab's full affine-group absorption first does not impose
such a restriction. We construct explicit images of *easy*, all-positive
source formulas whose residual difference systems contain any specified
binary column matroid as a minor. This result concerns a representation, not
the difficulty of deciding those formulas. It has no novelty or P vs NP
separation claim.

Here a binary matrix represents the matroid of its column labels: independence
means linear independence over GF(2). Columns may be zero (loops) or parallel.
Deletion discards a label. Contraction of distinct input column labels is
represented by quotienting the vector space by their span and removing those
labels. If they are dependent, contract an independent sublist and delete the
other labels, now loops. The target matroid is kept with its labels, even if
two surviving columns become equal in the quotient.

**Theorem.** Given a finite explicitly represented binary matrix \(B\),
there is a polynomial-time construction of a positive 3-CNF \(F\), every
clause containing three **distinct** variables, every variable occurring two
or three times, such that the following system contains \(M(B)\) as a minor:

1. Compile \(F\) by the [three-option, weight-two support reduction](support_threshold.md).
2. Apply the [affine-absorption rule](affine_frontier.md) to a fixed point, in any order.
3. Form the distinct nonzero within-group pairwise difference columns of the
   residual supports, in the quotient after absorption (a simple ground set).

The source family is satisfiable by setting every variable true. By “affine
absorption” we mean this particular exact coset rule and its reapplication in
the quotient. We do not include arbitrary logic preprocessing, extraction of
an immediately visible satisfying assignment, or a change of reduction.

## 1. Read off the residual difference system

For a literal occurrence \(j\), write \(V_j,C_j\) for its two unit coordinate
vectors: the value port and clause witness port. If its variable occurs \(k\)
times, number the slots of this variable cyclically; let \(E_j\) be the
separate equality port to its successor. In our construction \(k\ge2\), so
the incoming and outgoing ports are distinct even for a two-cycle. Set
\(Y_j=E_{\rm prev(j)}+E_j\).

The binary copy support \(\{V_j,Y_j\}\) has difference \(V_j+Y_j\). All
these differences are independent because each has its own \(V_j\) entry.
Write \(U\) for their span. Reducing modulo \(U\) replaces each \(V_j\) by
\(Y_j\); the \(C\) and \(E\) ports still form free ambient coordinates.
The choice of a different quotient basis makes no difference to dependencies.

A positive occurrence implication has the three pairwise differences
\(V_j,C_j,V_j+C_j\) before absorption, unchanged by local translations.
After absorbing copies they are \(Y_j,C_j,Y_j+C_j\). These are nonzero and
pairwise distinct. The three choices at a clause also remain distinct,
since its three \(C_j\)'s have independent coordinates. Each of these supports
thus has cardinality three, which cannot be the cardinality of a finite affine
space over GF(2). They remain nonaffine at every earlier stage of absorbing
copies: if two of their options had coincided modulo a smaller subspace of
\(U\), they would still coincide modulo \(U\). Every binary copy group is
absorbable. This proves that \(U\) is the *entire* span removed at the fixed
point, not a guessed subset of the solver's eliminations.

## 2. Contract to one symbol per source clause

In that residual difference system, contract the columns \(Y_j+C_j\) for
all occurrences. They are independent by their distinct \(C_j\) coordinates.
One can now read the images of the columns \(C_j\) as the vectors \(Y_j\).
For any fixed source variable \(v\), a linear relation on its occurrence
images is equivalent to

\[
 \sum_{j\text{ of }v} \alpha_jY_j=0
 \quad\Longleftrightarrow\quad
 \alpha_j=\alpha_{\rm next(j)}\quad\text{for every }j\text{ of }v.
\]

Indeed the coefficient at \(E_j\) is precisely the sum of these two bits.
Thus the sole independent relation within this cycle is “the sum of all
occurrence images is zero.” The cycles of different variables use disjoint
\(E\) ports; there are no cross-cycle relations yet. Unused complementary
ambient directions do not introduce dependencies on the retained columns.

For every clause \(c\), contract a spanning tree of its clause-selector
differences \(C_j+C_{j'}\) (two differences for three occurrences). This
identifies the three occurrence symbols as one symbol \(z_c\). Use an
independent sublist as above if some of the contracted columns have become
dependent. Retain the local column \(C_j\) at one slot of each clause and
delete unwanted columns. The represented vectors are now exactly the images
of the standard clause symbols in the *presented space*

\[
 Q(F)=\mathbb F_2^{\{\text{source clauses}\}}\bigg/
       \operatorname{span}\!\left\{\sum_{c\ni v}z_c : v\text{ a source variable}\right\}.
\]

This is equality of the full dependence spaces, not just a list of true
relations: the relations before the selector contraction were exactly the
cycle relations; the contraction adds exactly the span of the stated
pair identifications, all within the span of those symbols. In general
incidence should count occurrences modulo two. The formulas constructed
below have no repeated literal or variable in any clause. The selected
local unit-column labels are distinct before the contractions and are
different from the contracted differences. Deduplicating coincident columns
*before* this construction therefore does not remove the needed labels;
surviving parallel labels after contraction have ordinary matroid semantics.

## 3. Encode a prescribed binary presentation with these degrees

Let \(B\) have \(n\) labelled columns \(b_i\). In the free space on \(x_i\),
the quotient by \(\ker B\) represents exactly their dependencies, via
\(x_i\mapsto b_i\). Begin with the relations of any Gaussian-eliminated
basis for \(\ker B\). If that basis is empty, the original symbols still
have no relations. The following steps create the correct presentation on
our surviving labels without requiring long source clauses.

1. **Give every original label an incidence.** For each \(x_i\) add a
   fresh twin \(x'_i\) and the relation \(x_i+x'_i=0\). Forgetting the
   twins later leaves the original restriction unchanged. This also covers
   independent elements that participate in no kernel relation.
2. **Bound relation arity.** Keep relations with two or three symbols.
   For one with \(s>3\) distinct symbols, use a chain of ternary equations
   introducing fresh partial sums: \(a_1+a_2+t_1=0\), then force the next
   partial sum by adding one further \(a_i\), and finish with the last
   partial sum plus \(a_{s-1}+a_s=0\). Eliminating the \(s-3\) partials
   gives exactly the old relation. For a loopless target there is no
   singleton kernel relation: such a relation would say \(b_i=0\).
   To allow a singleton \(x=0\), replace it by \(p+q=0,\ x+p+q=0\) on
   two fresh symbols. This still forces \(x=0\), places no extra condition
   on the originals, and leaves a harmless free auxiliary direction.
   A zero equation may be discarded.
3. **Give every symbol at least two incidences.** Duplicate each surviving
   equation with a distinct *equation label*. This leaves its span unchanged.
   Every original and twin is covered by the twin equation; partial sums
   and loop auxiliaries are covered by their defining equations.
4. **Make each symbol occur in exactly three equations.** For a symbol
   appearing at \(k\ge2\) incidences, use one separate symbol \(u_j\) per
   incidence. Substitute it at that incidence, then add the \(k\) cyclic
   equalities \(u_j+u_{j+1}=0\). For \(k=2\), there are two different
   equality labels with the same pair of endpoints. All copies represent
   exactly the old symbol; eliminating copies adds no new relations on the
   originals. Each copy now appears in one substituted equation and two
   differently labelled equality equations.
5. **Read the presentation as a CNF.** Create one *Boolean variable* for
   each equation label. Create one positive clause per copied symbol,
   containing the three Boolean variables for its three equation incidences.
   This incidence transpose is the crucial direction: the relation labels
   are source **variables**, the symbol labels are source **clauses**.
   Each Boolean variable occurs two or three times because every equation
   has arity two or three. Every clause has three distinct variable labels.

Section 2 therefore yields exactly this final presentation. Keep one clause
column corresponding to one copy of each original \(x_i\), in the input
label order, and delete all other labels. By steps 1–4 their relations
are precisely \(\ker B\), as required. For a target with no columns, taking
the empty restriction suffices.

There are at most \(n\) basis relations, each containing at most \(n\)
symbols; all the splitting and duplication use only \(O(n^2+n)\) incidences,
symbols and labels. Computing the input kernel basis uses polynomial bit
time in the input matrix dimensions/explicit encoding. The CNF, the compiled
supports (including dense integer masks), the contraction list and its
Gaussian verification likewise have polynomial bit length and construction
cost. No search over formulas, variable assignments or minor embeddings is
needed in the construction.

## 4. Scope

For any proper minor-closed class of binary matroids, choose a represented
binary matroid outside the class. The residual difference system constructed
above has it as a minor, and so is outside the class too. For example the
Fano matroid rules out a uniform promise of graphicness. The point is not
merely failure of one proposed coordinate map: arbitrary linear change of
basis preserves these dependencies, and local translations preserve the pair
columns. This does **not** exclude nonlinear changes, deletion or branching
with problem-specific reasoning, decomposition and nontrivial handling of
general components, or algorithms which ignore this representation. All the
source formulas in this proof have a trivial all-true model. We prove neither
an exponential runtime for arbitrary solvers on them nor a separation of
complexity classes.

[The compiler and certificate verifier](../src/pnp_lab/minor_universality.py)
encode each further contraction and retained column by an original group and
pair of option indices. The verifier projects through the copy directions,
requires a fixed point, checks the selected nonzero columns belong to the
simple residual ground set, and compares the *labelled dependency spaces* of
the retained system and the target. In particular two systems of equal rank
need not have the same labelled dependencies. [The experiment](../experiments/binary_minor_universality.py)
and [its recorded cases](../results/binary_minor_universality.json) provide
finite, reproducible checks; the general result uses the argument above.
