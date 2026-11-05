# What binary implication paths add to the integer refuter

**Family theorem.** Fix a local integer scope bound $b\ge3$, and an integer $L>b$.
There are arbitrarily large satisfiable and unsatisfiable diamond-wrapped
3-CNFs with the following properties. On both sides, **every** raw
$b$-variable fragment has full integer affine lattice, and there is no
one-positive/one-negative private pivot. On the unsatisfiable expander
instances ordinary DAG resolution has exponential length. Yet a polynomial
deterministic search from the raw clauses finds width-three consequences
whose locally certified mod-two sum refutes every unsatisfiable member of
the family. The same projected parity equations give a checked raw model
on every satisfiable member, via one 2-SAT lift. Thus with growing polynomial
budgets the procedure **decides both sides of this family**. The construction uses fixed $b,L$; for the existing raw
integer checker one can take $b=15,L=16$. Feedback certificates on this
family only require three-variable scopes on the recovered formula.

There is also an **NP-complete failure class even with successful learning**:
on another family the very same path rule recovers every hidden clause and
the bounded-scope integer relaxation still cannot refute anything. Section 5
proves this; it does not depend on timeouts. The results concern specified
interfaces. They give neither a general polynomial SAT algorithm nor a lower
bound against one.

## 1. A width-three representation with no eligible private pivot

Use any connected simple cubic graph on $q$ vertices. One Boolean variable
per edge is subject to one parity equation per vertex, with right hand side
$d_v\in\{0,1\}$. Write the parity equation as the four proper 3-clauses
that forbid its four wrong local words. Call this formula $T$.
Odd total charge is impossible, since each edge occurs twice in the sum.
For even total charge, fix non-tree edges to zero and assign tree edges from
leaves to root to discharge each leaf's required parity. The root equation
then holds by the total-charge condition. This also gives a satisfiable
control on the same graph.

Write each source clause as $A\lor B\lor c$, where the three symbols are
signed literals on distinct variables. For each vertex choose the head $c$
among its three variables in rotation over the four clauses (for example
positions 1,2,3,1). Thus every incident variable stays in the first two
positions in at least two distinct start clauses at this vertex. Give each
clause its own new start variable $z$ and $L$ consecutive layers of two
new Boolean variables each. Add exactly:

1. the ternary start clause $A\lor B\lor z$;
2. implications from $z$ to both first-layer variables;
3. all four implications from each layer to the next;
4. the two implications from the last layer to the *signed* literal $c$.

Each implication $u\to v$ denotes the binary clause $\neg u\lor v$.
There are $2L+1$ private auxiliary variables, $4L$ binary clauses and
one ternary clause per gadget. The wrapped formula has
$3q/2+4q(2L+1)$ variables and $4q(4L+1)$ clauses.

A complete path implies $z\to c$, so any raw model satisfies the original
clause. Conversely, assign all private bits of this gadget the Boolean truth
value of literal $c$. A model of the original clause extends to a model of
the gadget. This is an exact existential projection and a concrete lift, not
equality of numbers of models.

For $L\ge2$, the start bit has positive/negative occurrence counts $(1,2)$,
first-layer bits $(1,2)$, intermediate bits $(2,2)$, and last-layer bits
$(2,1)$. No edge variable is private either: its original two occurrences
of each sign at each endpoint remain, with repetitions of the head literal
only increasing the counts. Independent polarity flips just exchange the
two counts. Thus the [old private pivot rule](modular_padding.md) cannot
start, despite abundant paths permitting small-width resolution. This does
not exclude unrestricted Davis–Putnam elimination or bounded variable
elimination policies other than this specific one.

## 2. Why the raw integer stage sees no obstruction

Let $S$ be any set of at most $b$ original **or auxiliary** variables of
the wrapped formula. Use all raw clauses whose variables lie in $S$, or
any subset of them. Each gadget has an entire layer absent from $S$:
otherwise $S$ contains at least one variable from each of the $L>b$
disjoint layers of that gadget.

For every assignment on the source edge variables there is a common choice
of helper values, independent of that assignment, satisfying the scoped
rows: in each gadget set the start and layers before a missing layer to one,
and all later layers to zero. There is no scoped edge through the gap.
The start clause is satisfied by its helper whenever present, and every
present last-layer implication has false antecedent. In particular, each
source coordinate in $S$ has two scoped models differing only there.

The same one-coordinate flip exists for each helper $h\in S$. For its
gadget choose source values making $A\lor B$ and $c$ both true, possible
because the three source variables are distinct. In this gadget set all
stages strictly before $h$'s stage to zero, and all strictly later stages
to one. Fix any peer of $h$ arbitrarily. No edge lies within a stage, so
either value of $h$ works. This also applies to the start as its own
stage, and to a last-layer bit. In every other gadget use the preceding
gap assignment. Private bits belonging to different gadgets are disjoint.

Consequently the differences of scoped Boolean models generate every unit
vector in $\mathbb Z^S$. Their affine integer lattice is exactly
$\mathbb Z^S$: there are no nontrivial entailed affine equalities or
congruences of *any* modulus. No global combination of just those rows
can refute the instance. Signed permutations preserve the result because
coordinate permutations and $x\mapsto1-x$ preserve the full integer
lattice. This is a theorem for the one-shot interface on raw scopes; it does
not cover arbitrary branching, extra inequalities, or deductions that feed
new nonlinear clauses into those scopes. The [integer theory](global_integer_theory.md)
defines that distinction.

## 3. Why one pass of learning recovers the useful clauses

Mark a variable as an anchor when it occurs in at least two different
proper ternary input clauses. The rotation guarantees that every edge
variable is marked. Each start bit appears in only one ternary, while
every interior helper appears in none. Thus the anchors on this family
are exactly the edge variables, without names, graph data or a map from
the generator.

In the binary implication graph a clause $\neg u\lor v$ supplies both
$u\to v$ and $\neg v\to\neg u$. From the positive start $z$, a
forward path through its private layers first reaches exactly the anchor
literal $c$. There are many such paths; one shortest path suffices.
Even continuing past $c$ introduces no other reachable anchor: any
outgoing edge there enters a reversed strip ending at a negative start
of a different gadget, which has no outgoing binary edge. This also
shows why the signed graph has no nontrivial strongly connected
component to contract. Polarity renaming is just a graph isomorphism.

Resolving $A\lor B\lor z$ successively with the binary clauses of
one path derives $A\lor B\lor c$ in $L+1$ steps, never exceeding
width three. Grouping the restored clauses on their three common variables
recovers precisely the four exclusions at each vertex. The eight local
words suffice to check the integer congruence
$\sum_{e\ni v}x_e\equiv d_v\pmod2$. Independent complementation of
edge variables changes the two incident charges together and preserves
their total parity. Sum the $q$ congruences with weight one. Every
coefficient of an edge is two and the total right side is odd, giving the
checked contradiction. This construction does not require the integer
diagonalization heuristic to choose a particular pivot sequence.

**Cost.** Keeping one successful path per gadget costs $4q(L+1)$
binary-clause references plus $4q$ start references. The arithmetic
suffix has $q$ three-coordinate rows with four cited learned clauses each.
Modulus two and the local weights, coefficients and RHS bits have constant
bit size. Unreduced global RHS sums need at most $O(\log(q+1))$ bits.
With canonical dense variable labels, the certificate occupies
$O(qL\log(qL+2))$ bits, counting indices as well as references.
This certificate bound alone would not bound discovery. Scanning and
grouping the input is polynomial. Breadth-first search per start visits
at most all literal vertices and all binary arcs; predecessor pointers
recover one path, without enumerating the exponentially many paths in one
strip. Even using the coarse per-start whole-graph bound takes
$O(q^2 L)$ graph visits on this family. There are exactly $4q$
restored clauses before any redundant copies; grouping equal scopes and
checking all eight assignments per group is polynomial. Labels, counters
and sorting have polynomial bit cost in the encoded input size. No
algorithm need enumerate expander graphs or supply the graph as advice to
recognize the recovered parity rows. Take search budgets large enough for
these bounds in the family theorem; a fixed execution cap can return
`UNKNOWN` on larger instances. No complexity claim for unrestricted
integer elimination follows.

### A deterministic procedure for *both* outcomes on this family

The [witness procedure](../src/pnp_lab/feedback_witness.py) first verifies
that every recovered scope is a complete parity half-cube and these are
all the recovered clauses. It performs binary Gaussian elimination on
dense temporary coordinates. On even total charge it obtains one anchor
assignment. Substituting that assignment into the original formula removes
or shortens every ternary start (two of its variables are now fixed).
The residual is a 2-CNF with unit clauses permitted. Crucially, **every**
satisfying parity assignment on the anchors has a raw extension here, by
the signed-head lift of Section 1. Thus the *first* parity solution is
enough: strongly connected components in the residual binary implication
graph give an extension, which the solver combines with the anchor
assignment and directly checks against the raw clauses. This uses no
generator-supplied choice of helpers. On odd total charge, an inconsistent
parity proposal does not itself label the raw input UNSAT: the separate
checked sum of Section 3 supplies the refutation. Neither branch needs
general integer diagonalization on this family.

Here are explicit polynomial budgets for the family procedure. Let $m$ be
the number of raw clauses and $n$ the number of raw variables, labeled
densely up to permutation. One projection pass has $4q$ starts. Since BFS
stops at anchors and each positive strip is private, *each binary clause
contributes just one visited arc*, for exactly $16qL$ total. The reverse
arcs are present but not traversed. There are $4q$ distinct lemmas and
$4q(L+1)$ path steps. On a SAT lift the residual implication graph has at
most $2n$ vertices and $2m$ arcs. Thus per pass, setting raw clause/active
variable/word-bit budgets to $m,n,n$, edge visits to $2m$, lemmas and
stored path steps to $m$ each suffices. A witness attempt followed by a
refutation can repeat the projection once; that is a constant factor.
Bounds here may be taken as upper bounds computed from the input, not as
advice giving the graph or its order.

Elimination has at most $q$ rows and $3q/2$ columns, so a conservative bit
bound for this stage is $O(q^3)$ for XORs, back-substitution and masks.
Residual construction and SCC traversal have polynomial bit cost in $n+m$;
packing and rechecking the raw $n$-bit output can cost more than the arc
visits alone but takes polynomial time. These costs, plus Section 3's
path discovery and proof writing, give a uniform polynomial total on both
sides **under the stated family promise and dense encoding**. The fixed
default resource caps in a command are not a completeness theorem at
unbounded input sizes. A binary-encoded huge unused coordinate label
would also require separate accounting if the witness were emitted as a
mask addressed by that label.

For arbitrary inputs, derived anchor constraints need only be *necessary*.
Consistency need not lift, there may be an unlearned constraint, or a fixed
proposal can leave clauses wider than two. Failing to extend one assignment
does not establish UNSAT: the witness branch then reports `UNKNOWN`.

## 4. The lower bound against resolution, and a stronger system that wins

Equirepresentability under existential projection alone does not transfer
a resolution lower bound. Here there is a **literal substitution**:
identify each positive helper in a gadget with its signed head $c$,
preserving negation, and leave edge variables untouched. Its ternary
axiom becomes exactly the source clause and all its binary axioms become
tautologies. Undo any external signed permutation before this substitution.

The [subclause projection lemma](width_transfer.md) translates any
ordinary DAG resolution refutation under this substitution with no
increase in maximum width or number of lines. Concretely, for each
non-tautological image keep a derivable subclause. At a resolution step,
if one mapped parent becomes tautological but the conclusion does not,
the nonpivot part of that parent contains the opposite mapped pivot.
Then the other parent's image already lies in the conclusion. If both
parents survive, reuse a stored subclause already contained in the
conclusion or resolve the two representatives on the mapped pivot.
A weakening step simply reuses its earlier representative. Axioms follow
from the displayed substitution; the empty final clause survives.
This argument permits noninjective maps and does not silently retain
tautological clauses as new axioms.

On connected cubic edge expanders, [Ben-Sasson and Wigderson, Theorem 4.4
and Corollary 4.5](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf)
give $\Omega(q)$ resolution width and $2^{\Omega(q)}$ resolution
length for the odd-charge core. One may use the cubic expander existence
argument in [the previous proof](robust_ceiling.md); this theorem does not
assert that every cubic graph, or a small benchmark graph, expands.
The bounds transfer to the wrapped input. For fixed $L$ it has linear
numbers of variables and clauses in $q$; binary indexing gives length
$O(q\log(q+2))$ bits. Exponential in the number of graph vertices is
not the same statement as exponential in the input bit length.

**Characteristic matters.** These very positive examples also admit
$O(qL)$-line ordinary polynomial-calculus refutations of degree at most
four over $\mathbb F_2$. Each width-three path step has the
[degree-four false-factor translation](correlation_polynomial.md); all
the participating clauses have bounded width, so it takes constant-size
arithmetic per step. At a recovered vertex, sum the four clause-falsity
polynomials. They are the disjoint indicators of the four words violating
$x+y+z=d_v$ modulo two. Their sum is exactly $x+y+z+d_v$: both sides
are multilinear and agree at every Boolean word. Sum the vertex identities
to get 1 from the clause axioms over $\mathbb F_2$. Line count and
monomial size are different: use a balanced addition tree for these linear
rows. At each depth every edge can occur in at most two partial sums, so the
total displayed monomial occurrences are $O(qL+q\log(q+2))$. This is an analytic
upper bound; it does not assert the existence of a recorded polynomial
trace for the benchmark. In particular, the separation above is **not**
a lower bound on matching-characteristic polynomial calculus, native XOR
solvers, general integer proofs, or preprocessing followed by Gaussian
elimination. It also does not show that non-binary moduli are necessary
on these Tseitin instances.

## 5. An NP-complete class with exact recovery but no local integer information

For any fixed $b\ge3$, take the [proper 3-CNF class of incidence girth
greater than $2b$](modular_barrier.md#a-fixed-scope-np-complete-subclass).
Every induced fragment on at most $b$ variables has a forest incidence
graph: a cycle there would use at most $b$ distinct variable nodes.
Every nonempty subset of $t$ clause nodes in such a forest uses
$2t+k$ variables, where $k\ge1$ counts components with a clause.
In particular, even after deleting any one chosen coordinate there are
at least $t$ adjacent variables for each such subset. Hall matching
therefore assigns the clauses distinct remaining variables. Make each
matched variable satisfy its own literal. This leaves the chosen
coordinate independently flippable, giving full integer difference
lattice by Section 2's unit-vector argument.

The cited repository reduction applies to **signed proper** ternary CNFs
and the bipartite clause-variable girth just used. For clarity, it fixes
a constant high-girth pin gadget for the fixed $b$ by deleting a clause
from a minimal high-girth contradiction. A private copy of this satisfiable
gadget supplies a forced-false literal to pad each implication of the
stretched occurrence-copy cycles. Its attachment is a bridge; outside these
gadgets every cycle must traverse a complete stretched segment. Thus the
output retains the required girth and preserves satisfiability. The gadget
size need not be polynomial in a varying $b$. See also Kun's general
[large-girth CSP constructions](https://arxiv.org/abs/0706.1701);
the concrete reduction fixes the exact encoding needed here.

Now wrap **three copies of each clause**, using disjoint helper sets and
cycling its head over all three literals. Even a variable occurring in
only one source clause is present in at least two *distinct* starting
ternaries. Every original variable is consequently an anchor. Every
hidden clause is recovered three times; after removing duplicates the
learned formula is exactly the original high-girth formula. The output
has nonempty binary implication paths whenever the source has a clause.
So this failure does not arise from the path frontend having nothing to do.

Each recovered scope of at most $b$ variables has only trivial integer
laws by the forest argument. The parity shortcut cannot produce an
inconsistent sum either: in particular, two different ternary clauses
on the same three variables would give a 4-cycle. Even a backend
collecting *all* integer affine equalities/congruences on *all* such
scopes receives no obstruction. For nonempty sources in this class the parity-model
attempt likewise stops because the recovered scopes are not complete parity
blocks. The combined procedure does not decide SAT versus UNSAT here. The algorithm may still report real differences in
the syntactic input or statistics; no indistinguishability claim about
arbitrary observers is made.

The fixed-$b,L$ wrapping is a polynomial-time satisfiability-preserving
reduction, so deciding SAT on these fully recovered inputs is NP-hard,
even with the promise of this form; a satisfying assignment is polynomial
evidence on the promised domain. For an ordinary NP-complete language,
use canonical ordered dense encodings of the constructed wrappers of
high-girth sources: source, wrapper labeling, and a satisfying assignment
are polynomial-size witnesses, and construction and the fixed-girth test
are polynomial to verify. This is a completeness obstruction for the
specified one-pass path-plus-local-integer rules. It is not an unconditional
superpolynomial time lower bound on SAT. The measured 31-variable control
uses a different finite core; it is not asserted to have girth greater
than $2b$.

## 6. Prior methods and the next test

Binary implication graphs and their use in SAT simplification have a
substantial prior literature; see [Heule, Järvisalo and Biere, SAT
2011](https://cca.informatik.uni-freiburg.de/papers/HeuleJarvisaloBiere-SAT11.pdf).
Here each reported path is just iterated ordinary binary resolution.
Recovering XOR constraints from implied clauses and combining CNF search
with Gauss–Jordan elimination are also established, e.g.
[Soos, Gocht and Meel, CAV 2020](https://pmc.ncbi.nlm.nih.gov/articles/PMC7363182/).
The present contribution is a scoped comparison with explicit witnesses
and a counterfamily for this particular interface; no priority claim
or superiority over these solvers is intended. Compared with the earlier
[skinny helper chain](modular_padding.md), these helpers do not have
one positive and one negative occurrence. Compared with its equality-guard
variant, there is no signed-equivalence component to contract.

The negative gate rules out extending the program by merely increasing a
*fixed* integer scope or improving search for the same binary paths. A next
hypothesis should introduce and cost an inference that still contributes
after the entire high-girth core is recovered, or change direction. Testing
a larger positive expander without an additional theorem would not answer
this question. The target for P=NP remains a complete uniform algorithm
with polynomial total bit cost on all unrestricted instances; see the
[solution criteria](solution_criteria.md).
