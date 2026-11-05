# Exact PC consequence spaces and separated polynomial subspaces

**Phase 20 status:** a finite ordinary-polynomial calculator with independent
derivation and closure checks, two general elementary lemmas, and explicit
failure controls. This note does not validate the external affine-DAG theorem
or prove a P versus NP separation. Its main purpose is to make the separated
subspace hypothesis measurable without confusing polynomial calculus with a
static axiom-multiple span.

The separate [common-annihilator argument](affine_dag_annihilator.md) develops
an independent affine-DAG consequence criterion. The exact spaces audited
here test its separated-subspace hypothesis and its finite controls; the
asymptotic mathematical argument is given in that note.

The source is [`src/pnp_lab/pc_subspace.py`](../src/pnp_lab/pc_subspace.py), the
experiment is [`experiments/pc_subspace.py`](../experiments/pc_subspace.py), and
the deterministic report is [`results/pc_subspace.json`](../results/pc_subspace.json).

## 1. The exact object being computed

Work over $\mathbb F_2$ in the ordinary polynomial ring on $n$ original
variables. A raw clause $C$ contributes its falsity polynomial

\[
 f_C=\prod_{x_i\in C}(1+x_i)\prod_{\neg x_i\in C}x_i,
\]

and the Boolean axioms are $x_i^2+x_i$. Repeated variables are retained in
ordinary monomials. In particular, this tool never replaces $x_i^2$ by $x_i$
without deriving the appropriate polynomial difference.

Write $P_t$ for the formal polynomial space of total degree at most $t$, and
let $C_B(F)$ be the polynomials with an ordinary PC derivation whose every line
has degree at most $B$. The rules are an eligible input axiom, zero, addition,
scalar multiplication, and multiplication by one variable when the resulting
degree is at most $B$. Over $\mathbb F_2$, the only nontrivial scalar is one.
An axiom of degree greater than $B$ cannot be inserted. These are the same
primitive bounded-degree rules inspected in the
[upstream interface audit](braun_resoplus_audit.md), not an assertion that PC
equals Nullstellensatz.

For $0\le k\le B$, define

\[
 q_B(k)=\dim P_k-\dim(C_B(F)\cap P_k).
\]

This is exactly the largest dimension of a linear subspace
$U\subseteq P_k$ satisfying $U\cap C_B(F)=\{0\}$. A complement exists by
finite-dimensional linear algebra. The calculator also supplies an explicit
complement spanned by ordinary monomials.

The ambient dimension is $\binom{n+B}{B}$. Consequently, the implementation is
a deliberately bounded research tool, not a polynomial-time algorithm in
the general input size. It returns `UNKNOWN` when a stated monomial, trace,
or work cap is reached. `COMPLETE` means that this finite consequence space
was determined; a completed run without $1$ is not a SAT conclusion.

## 2. Why the fixed point is the actual PC space

Order formal monomials first by total degree. Represent polynomials as
vectors and keep an echelon basis with the greatest nonzero monomial as
pivot. The following observation prevents a subtle degree-cancellation bug:

> If $W\subseteq P_B$ has such an echelon basis, the basis rows whose pivot
> degree is at most $t$ span exactly $W\cap P_t$.

To prove it, take a nonzero linear combination and the greatest pivot of any
basis row with nonzero coefficient. No other selected row can cancel that
pivot. Thus a combination involving a row of degree greater than $t$ cannot
lie in $P_t$.

Start with the span of every eligible axiom. For every newly found basis row
in $P_{B-1}$, multiply it by each original variable and insert the result by
elimination. Inserting and reducing may reveal new rows of degree less than
$B$, so they enter the same queue. At most $\binom{n+B}{B}$ independent rows
can be inserted.

Every generated row has a valid degree-$B$ PC derivation. At termination the
space contains all eligible axioms and is closed under multiplying any
polynomial in its intersection with $P_{B-1}$ by any variable. This follows
from the observation and linearity. Conversely, induction on a PC
derivation places every degree-$B$ consequence inside this closed space.
The two inclusions prove equality with $C_B(F)$.

The implementation records ordinary `input`, `boolean`, `add`, `multiply`,
and `zero` proof nodes. The independent checker first uses the earlier
[`parity_pc.py`](../src/pnp_lab/parity_pc.py) ordinary-polynomial replayer.
It then builds a sparse-set echelon basis, checks that every eligible axiom
belongs to the claimed space, and checks the multiplication closure just
described. The finder uses integer bitsets; the checker does not rerun the
finder or trust its reported ranks. A basis of derived rows without the
closure checks would establish only one of the two required inclusions.

For $U$, the checker computes the dimension of its whole span modulo
$C_B(F)$, not just nonmembership of individual generators. The canonical
complement consists of the monomials of degree at most $k$ which are not
pivots of $C_B(F)\cap P_k$.

The six test methods include every one of the 512 CNFs on two variables
formed from the empty clause, the four unit clauses, and the four proper
binary clauses. At each of $B=0,1,2$, their PC spaces are compared with an
independent exhaustive enumeration of all polynomials in the closure,
without Gaussian elimination. At $B=2$, the resulting quotient dimension
also agrees with the number of satisfying Boolean assignments. Further
tests reject missing basis rows, unsupported axioms, invalid degrees,
incorrect complements, and exhaustion mislabeled as a complete result.

## 3. A concrete PC versus static-span discrepancy

The static comparison space is

\[
 N_B(F)=\operatorname{span}\{m f:
    f\text{ is an original or Boolean axiom},\ \deg(mf)\le B\},
\]

where $m$ ranges over ordinary monomials. Allowing arbitrary polynomial
multipliers gives the same static span. In general it is a proper subspace
of $C_B(F)$, because PC may cancel high-degree terms before multiplying a
newly derived lower-degree polynomial.

For the clauses $(\neg x\lor\neg y)$ and $(\neg x\lor y)$, on variables
$x,y,z$, the two raw polynomials are $xy$ and $x+xy$. Their sum is $x$;
multiplication by $z$ derives $xz$ in PC through degree two. No eligible
original-axiom multiple through degree two contains the monomial $xz$,
so it is not in $N_2$. The complete finite audit gives

\[
             \dim N_2=5,\qquad \dim C_2=6.
\]

There is an equally explicit discrepancy for **refutation**, not just a
nonconstant consequence. Use unary pigeonhole with three pigeons and two
holes. Its six variables are $a_i,b_i$ for $i=1,2,3$. The clauses say each
pigeon occupies at least one hole and distinct pigeons cannot occupy the
same hole. Their ordinary polynomial axioms are

\[
 p_i=1+a_i+b_i+a_i b_i,\qquad
 a_i a_j,\ b_i b_j\quad(i\ne j),
\]

together with Boolean axioms. The report proves the exact PC refutation
degree is three: the complete degree-two space omits $1$, and the degree-three
space contains it.

The degree-three PC upper bound also has a short algebraic explanation.
For distinct $i,j$, use $a_jp_i$ and multiples of $a_i a_j$ to derive
$g_{ij}=a_j+a_jb_i$ through degree three. For the third pigeon $k$, derive
$g_{kj}=a_j+a_jb_k$. Multiplying $g_{ij}$ by $b_k$ and adding the collision
multiple $a_jb_ib_k$ gives $a_jb_k$; adding $g_{kj}$ yields $a_j$. The same
argument with the holes exchanged yields $b_j$. Combining these with $p_j$
and their product gives $1$. Every multiplication has actual degree at most
three.

In contrast, define a linear functional $L:P_3\to\mathbb F_2$ by

\[
 L(1)=1,\qquad
 L(a_i b_i)=L(a_i^2b_i)=L(a_i b_i^2)=1,
\]

and assign zero to every other formal monomial of degree at most three.
It annihilates every eligible monomial multiple of the raw and Boolean
axioms. For example, $L(p_i)=1+1=0$; multiplying $p_i$ by one of its own
variables produces two of the listed moments, and multiplying by a variable
of another pigeon produces none. The collision and Boolean cases follow
directly from the displayed values. Hence $1\notin N_3$.

The report includes this ten-entry moment witness, a checker which tests
every eligible original-axiom multiple, and a complete ordinary-PC closure
certificate. The exact dimensions are:

| Formula / degree | Formal ambient dimension | Static rank | Actual PC rank | Maximum separated dimension in the indicated $P_k$ |
|---|---:|---:|---:|---:|
| PHP(3,2), $B=2,k=2$ | 28 | 15 | 15 | 13 |
| PHP(3,2), $B=3,k=3$ | 84 | 82 | 84 | 0 |

Thus substituting a degree-three static Macaulay matrix for the actual PC
space would falsely leave a nonzero separated space on an input which
already has a degree-three PC refutation. No field-independent claim is
inferred from this F2 implementation.

## 4. Padding can preserve degree while shrinking the relative dimension

The following elementary observation holds over any field. Let $F(x)$ be a
polynomial base including the Boolean axioms for $x$, and form

\[
 F'(x,y)=F(x)\cup\{y_1,\ldots,y_r\}\cup
                  \{y_j^2-y_j:1\le j\le r\}.
\]

For $B\ge1$ and $0\le k\le B$, restriction $\rho:q(x,y)\mapsto q(x,0)$
induces an isomorphism

\[
 \frac{P_k(x,y)}{C_B(F')\cap P_k(x,y)}
       \;\cong\;
 \frac{P_k(x)}{C_B(F)\cap P_k(x)}.
\]

**Proof.** Restriction preserves every ordinary PC rule without increasing
degree. A multiplication by a deleted variable becomes the zero polynomial;
the new unit and Boolean axioms become zero. Thus it sends $C_B(F')$ into
$C_B(F)$. Conversely, every monomial involving a $y_j$ can be derived from
the unit axiom $y_j$ within its own degree. Therefore $q-\rho(q)$ belongs to
$C_B(F')$ for every $q\in P_k(x,y)$, and old derivations remain valid in the
larger base. These two facts establish the quotient isomorphism. The same
restriction and embedding prove equality of the full minimum refutation
degrees whenever the base is inconsistent. ∎

In the experiment, adding three forced-zero variables to PHP(3,2) increases
$\dim P_2$ from 28 to 55, while $q_2(2)=13$ and the exact PC refutation degree
three remain unchanged. A degree lower bound alone therefore supplies no
automatic near-full-dimensional separated space in the enlarged ambient
variable count. The observation does not refute stronger statements which
also assume expansion, irredundancy, or a quantitative relation between
degree and the number of relevant variables.

A separate warning control uses the inconsistent clauses
$\neg x,\neg y,\neg z,(x\lor y\lor z)$ at $B=2$. Its quotient is
one-dimensional because the contradictory width-three axiom is ineligible.
This is **not** an instance of the external generic criterion, whose degree
budget includes its input width. The report labels the omission explicitly.

## 5. Nonmembership of individual generators is insufficient

For one positive clause $x_1\lor\cdots\lor x_r$, every squarefree monomial
$x_T$ has value one on the satisfying all-ones assignment. Soundness alone
therefore shows that none of these monomials belongs to the PC consequence
space. But their span contains the nonzero input polynomial

\[
                \prod_{i=1}^r(1+x_i)=\sum_{T\subseteq[r]}x_T.
\]

When $B\ge r$, that span has nonzero intersection with $C_B$. The finite
$r=3$ control checks all eight individual nonmembers and then finds
intersection dimension one for their joint eight-dimensional span.
Removing the full-support monomial gives the seven-dimensional separated
empty-support span in this example.

This rules out a tempting but invalid shortcut when testing a proposed
large $U$: checking every chosen basis polynomial individually does not
check every linear combination.

## 6. Two finite controls for empty clause support

For a variable set $T$, the experiment uses the actual clause-set support

\[
 \operatorname{Sup}_s(T)=
  \bigcup\{A:\ 1\le |A|\le s,\ \partial A\subseteq T\},
\]

where $\partial A$ consists of variables occurring in exactly one clause
of $A$. It does not replace this union by the clauses individually contained
in $T$.

The two SAT controls have six variables, $B=k=3$, and $s=12$. Every existing
clause set is explicitly checked to satisfy $|\partial A|\ge |A|/2$ and
$|N(A)|>7|A|/4$. There are no clause sets larger than the listed two or three
clauses, so the expansion requirements for larger sizes are vacuous. These
are not asymptotic UNSAT instances.

| Proper linear 3-CNF support | Empty-support degree-three monomials | Empty-support monomials through degree three | Exact joint intersection with $C_3$ |
|---|---:|---:|---:|
| $(1,2,3),(4,5,6)$ | 18 | 40 | 0 |
| $(1,2,3),(3,4,5),(5,6,1)$ | 16 | 38 | 0 |

In the second control, $T=\{2,4,6\}$ contains no individual clause support.
Nevertheless, the boundary of the three-clause set is exactly $T$, so
$\operatorname{Sup}_{12}(T)$ contains all three clauses. This demonstrates
why a singleton-clause approximation to support would use the wrong set of
candidate monomials.

The checker verifies separation of each entire displayed span by a joint
rank calculation. The finite result is consistent with an empty-support
reduction argument; it does not by itself establish that argument for an
unbounded expanding family.

## 7. Reproduction and limits

```sh
PYTHONPATH=src python -m unittest tests.test_pc_subspace -v
PYTHONPATH=src python experiments/pc_subspace.py --out-dir reproduced/phase20/pc_subspace
```

The experiment completes nine spaces, independently checks their closures,
retains a complete PHP degree-three certificate and the explicit static
moment witness, and rejects three deliberately incomplete basis claims.
The largest ambient space has dimension 220. The two empty-support spans
have dimensions 40 and 38.

The implementation does not decide an asymptotic dimension lower bound for
the phase-16 expanding UNSAT family, handle arbitrary fields, establish a
polynomial-time bounded-degree search when the bound grows with input size,
or certify any uninspected dependency of the external affine-DAG theorem.
It supplies exact small-instance checks and guards against specific invalid
inferences in that research direction.
