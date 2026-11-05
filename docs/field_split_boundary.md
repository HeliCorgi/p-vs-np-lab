# One Boolean split can switch the useful characteristic

**Result.** There is a family of ordinary Boolean 3-CNFs with polynomially
discoverable refutations consisting of **one Boolean case split** and one
local-table/modular-sum certificate per side. The two certificates use moduli
2 and 3. For the *same* family, ordinary polynomial calculus (PC) requires
degree linear in the variable count over **every field**, even a field chosen
after seeing the input. The constants are uniform. These formulas therefore
give an alternative outside the [one-prefix/one-sum theorem](feedback_simulation.md);
they are not successful high-digit single sums. They also do not give an
algorithm with a completeness guarantee for general SAT.

**Prior work and scope.** The two-prime disjunction principle is known.
[Lichter–Pago, Sections 3–5](https://arxiv.org/abs/2407.09097) combine
mod-2 and mod-3 Tseitin instances in a CSP or-construction and discuss why
pinning a partial solution changes the affine algorithm's power.
[Conneryd–Ghannane–Pang, Section 1.3, footnote 2](https://arxiv.org/html/2511.17272v1)
explicitly infer linear PC degree in every characteristic for that
construction by restriction to a wrong-characteristic branch. The
wrong-characteristic algebraic bound comes from
[Buss–Grigoriev–Impagliazzo–Pitassi (BGIP), Sections 2, 6–7, Theorems 10 and 15](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/lineargaps/journalfinal.pdf).
Our contribution here is a reproducible instance and proof format in the
lab's original width-three Boolean language, plus the degree transfer for
its exact encoding. We do not import all CSP hierarchy bounds from the
Lichter–Pago encoding, and claim no new all-field disjunction principle.

## 1. A selector that does not create width-four clauses

Take a connected simple cubic graph $G$ on $N$ vertices; orient its edges.
Subdivide one directed edge $u\to v$ into $u\to r\to v$, giving graph
$G'$. There are two disjoint copies of the edge variables of $G'$.
On bank $p$, the variable on edge $e$ represents $t_e\in\mathbb Z_p$.
At a vertex require outgoing minus incoming flow to equal its charge.
Bank 2 uses one Boolean per edge. Bank 3 uses three one-hot bits per edge,
with one positive ternary domain clause and three pairwise exclusions.
A forbidden local edge-state tuple contributes the clause blocking it,
using one literal per incident edge. No algebraic instructions are input.

A single original Boolean variable $z$ is shared by the two banks. In
bank 2 put base charge 1 at old vertex 0, zero elsewhere. In bank 3 put
base charge zero everywhere. At the new vertex $r$ in both banks, increase
the required charge by $z$. For each violated tuple of the two incident
edge states and the bit $z$, add its blocking **ternary** clause. Thus
every raw input clause has at most three literals; this construction does
not append a guard literal to a pre-existing ternary clause.

In a connected graph the edge equations extend to a global flow exactly
when the charges sum to zero. Necessity sums the vertices; sufficiency sets
non-tree edges to zero and solves the edges of a spanning tree from the
leaves to the root. The canonical unsatisfiable formula has the following
two residuals:

| $z$ | bank 2 total mod 2 | bank 3 total mod 3 | unsatisfiable bank |
|---|---:|---:|---|
| 0 | 1 | 0 | 2 |
| 1 | 0 | 1 | 3 |

Setting both base charges to zero gives a satisfiable control with $z=0$
and both flows identically zero. A signed renaming, variable permutation
and clause/literal reordering preserve the arguments (the two branch
labels can swap). The code uses $1+4(3N/2+1)$ Boolean variables and
linearly many constant-width clauses.

## 2. Polynomial discovery and independent verification

The [refuter](../src/pnp_lab/field_split.py) receives only the raw formula.
It proposes variables whose removal increases the number of connected
components of the primal graph, trying balanced cuts first. The true
selector is always among these variables: each bank is connected and
nonempty without it, and the selector joins them before removal. It is
unnecessary to recover edge names or determine which prime belongs to
which side in advance. For each candidate, restrict to false and true;
on each restricted formula try the existing local affine
[modular solver](modular_hull.md) over 2 and 3. A successful proof stores
the selector and the two modular certificates. The checker independently
reconstructs **both** restrictions from the original input and checks the
two local-law sums against the respective residual clause IDs. Statistics
and articulation status are not checker premises. A missing proof, a
failed branch or an exhausted budget does not establish SAT.

Why the implemented scope search suffices on the family: each bank-2
star has its incident two or three variables as an input support and
excludes exactly the wrong-parity patterns. For bank 3, the domain
ternary and its three binary exclusions place every true indicator block
among the proposed blocks. Some forbidden state tuple on every star has
one literal per incident edge. Expanding each such coordinate to its
proposed whole block includes the entire star (at most $3\cdot3=9$
bits). The restrictions at $r$ leave the appropriate two-edge tuple
exclusions. The modular solver enumerates the genuine Boolean models on
each proposed scope; the divergence equation on a star belongs to their
affine consequences in the matching characteristic. On a trit edge its
value is represented by $X_{e,1}+2X_{e,2}$. Under a polarity flip replace
the original indicator by one minus its new bit. The signs and constant
terms then still cancel in the sum of all vertex laws, except for the
nonzero charge. The computed local row bases and Gaussian elimination span
this contradiction. Thus no particular basis or pivot sequence is assumed.

Cut discovery as implemented takes at most $O(a(a+m))$ adjacency visits,
where $a$ counts occurring variable labels and $m$ clauses. At most $a$
candidates yield at most $4a$ calls to the field solvers. Enumerating
scope proposals is polynomial: at most three coordinates per raw support
are expanded, each from at most $O(m+1)$ options, and each retained table
has at most 512 cells. Sparse elimination and its proof combination vectors
have polynomially many rows and columns over fixed finite fields. Using
the explicit input length to pay for sorting, label bits, proof copies and
replay therefore still gives polynomial total bit cost. Use
`max_candidates=None, max_scopes=None` (or sufficient polynomial bounds)
for the family theorem; the default candidate limit can of course interrupt
search on other inputs. This is a polynomial refutation scheme on the
specified unsatisfiable family; its failure on arbitrary input is UNKNOWN.
The satisfying controls are checked by their original Boolean words, not
claimed as successes of this refuter.

## 3. The lower-bound graph and arbitrary charges

For the asymptotic claim choose $G$ from any cubic expander family with
constant edge expansion $h>0$: for $0<|U|\le N/2$, the cut has at least
$h|U|$ edges. For example the degree-three case of
[Morgenstern's construction](https://doi.org/10.1006/jctb.1994.1054)
supplies an explicit expander family; the refuter needs no graph advice.
The measured prisms below are not asserted to be such a family.
Subdividing a single edge preserves a constant lower bound $h'\ge h/2$.
Indeed for $|U'|\le(N+1)/2$ the integer size of $U'\cap V(G)$ is at most
$N/2$ ($N$ is even). Every original crossing edge contributes at least
one crossing edge in the subdivision. If $|U'|\ge2$ this gives
$h(|U'|-1)\ge h|U'|/2$; a singleton has degree at least 2, and $h\le3$.

Here is the BGIP small-cut argument adapted to the actual oriented graph,
the degree-two port and arbitrary vertex charges. This step matters:
the all-ones homogeneous presentation of their graph equations has a
congruence condition on the vertex count. We do not impose it on cubic
graphs or assume that a different Boolean encoding is automatically hard.

Let $K$ be any field with characteristic different from the group's
prime $p$. Pass if necessary to a splitting field $E$ of $Y^p-1$ over
$K$. It has distinct roots and a primitive root $\omega$ of order $p$.
This includes characteristic zero. Put one multiplicative coordinate
$Y_e$ on each canonically oriented edge. Define the multiplicative
polynomial axioms (there are **no** Boolean axioms on these coordinates):

\[
 Y_e^p-1=0,\qquad Y^{B^T1_v}-\omega^{d_v}=0 .
\]

Here $B$ is signed vertex-edge incidence over $\mathbb F_p$ and
exponents use their representatives $0,\dots,p-1$. Thus an incoming
edge has exponent $p-1$ in the star; no reciprocal is a proof operation.
For any two ordinary monomials of degree at most $k$, reduce just their
exponent vectors modulo $p$, obtaining $f,g\in\mathbb F_p^{E(G')}$.
Their difference has support at most $2k$. Identify their classes if
$f-g=B^T t$ for some vertex labeling $t$ supported on fewer than
$|V(G')|/2$ vertices. Such a $t$ is unique, since two candidates agree
at some zero coordinate and their difference is constant on a connected
graph. Moreover the cut of $\operatorname{supp}(t)$ is contained in
$\operatorname{supp}(B^Tt)$. For $k<h'|V(G')|/8$, every such labeling
therefore has support at most $2k/h'<|V(G')|/4$.

This makes the class relation transitive: two witnesses add to one
supported on fewer than half the vertices. Negation supplies symmetry.
In each class choose one representative exponent vector $g$ and one
formal basis symbol. Send a monomial with vector $f$ to that symbol
times $\omega^{\sum_v d_v t_v}$, using the unique witness for $f-g$.
Extend linearly to ordinary polynomials of degree at most $k$. The
phase ratio of the images of **any** related pair depends only on their
witness: uniqueness and addition of the small witnesses prove this
independently of the chosen representative.

Every available axiom maps to zero: exponents differing by $p$ on an
edge have identical normalized vectors; the star difference has witness
$1_v$ and hence exactly phase $\omega^{d_v}$. Linear combinations preserve
the kernel. Multiplying a source polynomial of degree below $k$ by $Y_e$
preserves the kernel too: within each class of its monomials, shifting
the exponents by the same unit preserves their pairwise differences and
phase ratios, so the cancellation in that class persists. The target
classes need not be distinct for this to hold. Finally 1 maps to a
nonzero basis vector times a unit. No degree-$k$ PC refutation of the
multiplicative system exists. We use sufficiently large graphs; a wide
axiom unavailable at degree $k$ need not be checked at that degree.

## 4. Transfer to the actual Boolean clauses and to the switched CNF

Over $E$ replace each trit indicator by its Lagrange polynomial
\[
  I_a(Y_e)=\prod_{b\ne a}
      (Y_e-\omega^b)/(\omega^a-\omega^b),\qquad a,b\in\mathbb F_p .
\]
On the root grid these take the intended one-hot values. For $p=2$ use
$I_1$ for the single original edge bit. Each substitution has degree at
most $p-1$. We must actually derive the substituted Boolean axioms and
clause polynomials; assuming only an equisatisfiable encoding would not
preserve degree.

* For edge Boolean/domain axioms the substituted polynomial vanishes on
  the whole one-edge root grid. Division by $Y_e^p-1$ derives it from
  that axiom without increasing its formal degree.
* For a star clause, let $H$ be its substituted falsity polynomial and
  $P$ the relevant multiplicative star axiom. Both have degree at most
  $3(p-1)$ on at most three edge coordinates. On the local root grid,
  $H=0$ whenever $P=0$, by the construction of the forbidden tuples.
  Define a table equal to $H/P$ when $P\ne0$ and zero otherwise. Tensor
  Lagrange interpolation gives a polynomial $Q$ agreeing with the table,
  of degree at most $3(p-1)$. Derive $QP$ by expanding $Q$ into
  monomials and successively multiplying $P$ by their variables, then
  adding. $H-QP$ vanishes on the grid. Reduce its monomials by
  $Y_e^p=1$ coordinatewise, using a monomial times $Y_e^p-1$ in each
  step. The remainder, of individual degrees below $p$, vanishes
  identically by grid interpolation. This derives $H$ at ordinary
  degree at most $6(p-1)$. Domain clauses also fit this bound.
* A Boolean PC derivation of degree $d$ now translates line by line:
  linear combinations translate directly; multiplication by a substituted
  variable uses the monomials of $I_a$. All formal intermediate degrees
  in these multiplications are at most $(p-1)d$. Repeated powers are
  charged before reduction. Thus a degree-$d$ Boolean refutation would
  yield a multiplicative refutation of degree at most
  $\max(6(p-1),(p-1)d)$ over $E$. A proof over $K$ is already a proof over
  $E$, so adjoining roots does not weaken the inferred lower bound over $K$.

Given a putative PC refutation of the full switched formula over $K$,
choose the hard branch for that particular field: if
$\operatorname{char}K=2$, set $z=1$ and leave the mod-3 bank; otherwise
set $z=0$ and leave the mod-2 bank. Fix *every* variable in the other
bank to a satisfying flow for the chosen selector. A restricted clause
polynomial becomes zero or exactly the falsity polynomial of its residual
clause. The remaining axioms are precisely those of the active Boolean
flow on $G'$, with total charge 1. A constant restriction of a PC proof
cannot raise its degree: variable multiplications become variable
multiplications, scalar multiplications, or zero. Independent signed
renamings also preserve degree by the substitution $x\mapsto1-x$.
The preceding bound forces $d=\Omega(N)$, uniformly in the chosen field.
There are only $O(N)$ Boolean variables in the full CNF. This proves the
claimed all-field lower bound, not a lower bound on arbitrary SAT methods.

## 5. Reproducible finite controls and limitations

[The experiment](../experiments/field_split.py) tests signed/reordered
6- and 12-vertex prism pairs. The root-only field solvers are inconclusive
in both fields on all four examples. On both UNSAT inputs, discovery finds
one selector and independently checks both branches, using a different
characteristic on each. On the balanced siblings it returns UNKNOWN and
the experiment verifies an actual satisfying word against every original
clause. It also checks the local interpretation against the actual
one-hot/one-bit clause generator for all 60 combinations of group,
two/three-edge orientation and charge: 916 root-grid tuples over
$\mathbb F_3$ (group 2) and $\mathbb F_4$ (group 3). These checks do not
measure PC degree or prove the unbounded result. The [tests](../tests/test_field_split.py)
reject swapped branches, incomplete or modified certificates, and attempts
to treat a cap as a proof.

Case splitting is sufficient, but not necessary, to expose this conflict.
On the unrestricted formula the raw vertex laws of the two banks sum to
$z\equiv1\pmod2$ and $z\equiv0\pmod3$. Their Chinese-remainder consequence
is $z\equiv3\pmod6$, which is consistent over the integers but incompatible
with $z\in\{0,1\}$. Keeping this last column and checking its Boolean domain
exits the no-split rule that requires **all columns to cancel**. Equivalently
on this family, transfer the mod-2 unit into the mod-3 system using its
meaning on Boolean values. The [existing unary Boolean bridge](mixed_modular.md)
already gives an independently checked refutation on both finite UNSAT
controls in the report, without case splitting. The case split and this
Boolean transfer are alternatives here; no general equivalence is claimed.

The fixed-field PC lower bound alone does not rule out a single global
high-digit certificate. The independent [coprime signed marginal
argument](coprime_pseudomarginals.md) excludes even arbitrary detecting digits in
the specified bounded-width/bounded-scope, terminal-cancellation system.
The constructed incidence graph is not the expanding proper
linear *clause-support* family used for localization: expansion here is
of the underlying flow graph. A one-cut refuter has no general bound on
the number of further case splits needed on unrelated 3-SAT inputs.
