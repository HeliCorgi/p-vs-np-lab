# A support-sensitive lower bound for parity queries with integer terminal proofs

This extends the [phase-18 variable-query argument](conditional_localization.md)
to parity questions on several original coordinates. The leaf is still allowed
an arbitrarily long narrow resolution proof followed by local affine integer
laws and one global weighted contradiction. The modulus, coefficient sizes,
and number of those laws are unrestricted. The cost charged to a fresh parity
question is the number of its newly exposed coordinates, not its rank as one
binary equation.

The result is a mathematical paper proof. The finite audit below checks its
extension construction; it does not infer the asymptotic bound from experiments.
The proof uses the same closure, matching, and two-sided counting devices as
phase 18. No priority claim is made for those devices or for parity-tree lower
bounds in established proof systems; the [prior-work note](parity_query_prior_work.md)
distinguishes those systems and their terminal rules.

## 1. Exact proof model

The input is a CNF on its original Boolean coordinates. Each internal node asks

\[
                 c+\bigoplus_{v\in Y}x_v\in\mathbb F_2.
\]

Repeated occurrences are cancelled before defining the support $Y$, and signs
are incorporated in the constant $c$. Both answers have child subtrees. Queries
may be chosen adaptively. An empty support is a constant question.

At a leaf, let $P$ be the conjunction of the parity answers on its path.
We allow the following precise conditional certificate.

1. Ordinary resolution and weakening from the original CNF and Boolean clauses
   implied by the path's linear context $P$, with every used resolution line of
   width at most $w$. Such a context clause has a checkable justification:
   adjoining the Boolean values that falsify it makes the path's binary linear
   system inconsistent, as certified by Gaussian elimination. Thus arbitrary
   linear combinations of **path queries** are allowed; learning a new parity
   from the CNF requires an additional rule not present here. Full truth-table
   CNF encodings of individual queries are a special case. Only actually used
   clauses need appear in the proof. There are no extension coordinates or an
   unrestricted semantic inference from the whole UNSAT formula.
2. An affine integer equality or congruence, including modulus zero for an exact
   equality, can be certified by all Boolean models of a cited local set of raw
   or learned clauses on a scope of at most $b$ coordinates. The table may also
   discard any local word having no extension to a Boolean solution of $P$;
   Gaussian elimination with that word pinned checks this exclusion. This
   includes adding an answered query to the table when its whole support fits
   there, and permits wider path constraints through their projections. Beyond
   these explicit context exclusions, local validity and the final weighted
   sum use [the phase-17 rules](feedback_simulation.md).
3. The terminal contradiction is one sound integer weighted sum of those laws.
   Direct use of the path's parity congruences as additional arithmetic premises
   is also harmless for this theorem, even when a query support exceeds $b$.

No intermediate proof is shared between incomparable tree branches. A prefix
*within one leaf* can be a DAG of arbitrary length. Arithmetic-to-Boolean domain
checks, arbitrary multiplication of derived rows, a new rule for learning parity
equations from the raw CNF, and a different terminal proof language are not
silently included. A system may add another rule only after proving the required
restriction property and residual lower bound for it.

The property of this model used below is concrete: if a partial assignment fixes
every coordinate mentioned by every path query, with the recorded answers, then
all context axioms become true. Indeed, every completion of that assignment
satisfies $P$, hence satisfies each context clause; after restriction the clause
is satisfied or a tautology. Restricting the leaf certificate gives a phase-18
certificate on the remaining original CNF, with width at most $w$ and local
scope at most $b$. Ordinary resolution restricts to derivable subclauses without
increasing width. In every local integer row subtract the contribution of the
fixed bits from its right side. Local validity is preserved by restoring those
bits: every restored local word can be combined with the already assigned $X$
and arbitrary other free bits to satisfy $P$, so none is lost to a context
exclusion. In the final sum the right-side shift is the aggregate coefficient vector
dotted with the fixed bits, so the contradiction is preserved. A path congruence
reduces to an integer identity or a true constant congruence. These are the same
restriction arguments used in phase 18.

## 2. General theorem for expanding bounded-arity CNFs

Let $F$ have proper, non-tautological raw clauses of width at most $r$, where
$r\ge2$. Treat raw clauses as distinct IDs. Assume that for an integer $s\ge1$,

\[
       |N(U)|>\alpha |U|\qquad(1\le |U|\le s),
       \qquad \alpha>\max(1,r/2).
\]

Choose a real number $\beta$ with

\[
       \max(1,r/2)<\beta<\alpha,
       \qquad \delta=2\beta-r>0.
\]

Write

\[
 R=\max\left(1,\ 2\left\lfloor\frac w\delta\right\rfloor,
                  \ 2\left\lfloor\frac b\delta\right\rfloor\right).
\]

If $s\ge R$ and every query support has size at most the positive integer $q$,
then every finite refutation tree of the stated kind has at least

\[
 \boxed{\quad 2^K\text{ leaves},\qquad
       K=\left\lfloor\frac{(\alpha-\beta)(s-R)}q\right\rfloor.\quad}       \tag{1}
\]

When $s<R$, only the trivial bound of one leaf is asserted by this formula.
The theorem does not require an efficient procedure for recognizing expansion,
finding the closure, or computing the adversary's matching. Those are existence
objects in a lower-bound proof, not claimed SAT algorithms.

### Maintain a closure around the coordinates already exposed

Maintain a set $A$ of exposed variables, a raw clause set $C$ of size at most
$s$, and an assignment on $X=A\cup N(C)$ satisfying every clause of $C$.
Take $C$ inclusion-maximal among eligible supersets of the preceding closure:

\[
                       |N(C)\setminus A|\le\beta |C|.          \tag{2}
\]

At the beginning $A=C=\varnothing$. Expansion ensures that no nonempty raw
set of size at most $s$ is eligible then. If $C\ne\varnothing$, expansion and
(2) give

\[
       \alpha|C|<|N(C)|\le |A|+\beta|C|,
       \qquad |C|<\frac{|A|}{\alpha-\beta}.                    \tag{3}
\]

The weak inequality with $\le$ holds also for the empty closure. Maximality
gives the following residual expansion, for every nonempty raw $U$ disjoint
from $C$ and of size at most $s-|C|$:

\[
                         |N(U)\setminus X|>\beta |U|.         \tag{4}
\]

Otherwise $C\cup U$ would be an eligible larger closure. Counting its neighbors
outside $A$ is legitimate even when $U$ and $C$ share variables: the new part
is exactly $N(U)\setminus(A\cup N(C))$.

### A new parity can be answered both ways

If its support $Y$ is contained in $X$, answer the parity using the existing
assignment; no set changes. Otherwise choose one $x\in Y\setminus X$, put

\[
                  A'=A\cup(Y\setminus X),
\]

and extend $C$ to an inclusion-maximal eligible $C'$ for $A'$. The old $C$
remains eligible, so such an extension exists. For every nonempty
$U\subseteq C'\setminus C$, (4) applies. Since $\beta>1$, its integer number
of fresh neighbors is at least $|U|+1$. Removing just $x$ still leaves Hall's
condition. There is consequently a matching of the newly absorbed clauses
to distinct variables outside $X\cup\{x\}$.

Assign each matched variable so that it satisfies its matched clause. Retain
all old values and fix all other coordinates of
$X'=A'\cup N(C')$ except $x$ arbitrarily. Every clause of $C'$ now holds for
**either** value of $x$. All coordinates of $Y$ are in $X'$. Changing $x$ alone
changes the parity answer, so the same matching and all other new values work
for both children. All previous answers remain true because their entire
supports were already in $X$.

This is the step that a rank-only argument misses. One answered parity gives
one branch bit, but this particular strategy exposes all its fresh support.
It adds $|Y\setminus X|\le q$ variables to $A$. It does not assume that
arbitrary assignments to all these variables could be extended.

### Why the terminal integer proof still cannot close

Restrict $F$ by the full maintained assignment on $X$. Clauses in $C$ disappear.
In any nonempty family of $t\le s-|C|$ surviving raw clauses, (4) yields more
than $\beta t$ free neighbors. There are at most $rt$ incidences. If $h$ is
the number of variables occurring in exactly one of those clauses, then

\[
                 rt\ge 2|N(U)\setminus X|-h,
                 \qquad h>(2\beta-r)t=\delta t.              \tag{5}
\]

Also (4) gives at least $t+1$ free neighbors. Thus every small residual
subfamily has a matching avoiding any one chosen free coordinate. Duplicate
residual clauses, if normalized, can use one raw representative each.

The [common-support proof](support_localization.md) now applies to this residual
CNF. It needs boundary expansion to bound and pool semantic supports, and this
one-coordinate Hall surplus to obtain coordinate flips. Residual clauses need
not still have the original width. As soon as $s-|C|\ge R$, every local
scope after any width-$w$ resolution prefix has full affine integer lattice.
Every permitted local affine law is therefore an identity on the whole
integer lattice, so all such rows have a common integer solution, independent
of their moduli. No final weighted sum can contradict it.

The actual path might not name all coordinates of $X$. This causes no gap:
its query supports are entirely assigned in $X$, with the recorded answers,
and the restriction property in section 1 would take an actual closing leaf
to the impossible residual certificate just described.

### Count two-sided offers, not merely depth

After $j$ offered questions, $|A|\le qj$. For $j\le K$, (1) and (3) imply

\[
            |C|\le\frac{qj}{\alpha-\beta}\le s-R.
\]

No compatible leaf can close before the $K$th offered question. Questions
already fixed by $X$ have one compatible successor; a fresh question has two
compatible successors by the construction. In a finite tree, splitting mass
equally on these offers gives $2^K$ distinct compatible prefixes at the $K$th
offer, each with a different descendant leaf. When $K=0$ this is simply the
trivial one-leaf statement. A long path alone would not establish this count.

More precisely, the proof charges

\[
             |A|=\sum_{\text{offered questions}}|Y\setminus X_{\rm before}|.
\]

If the reserve threshold has not been exceeded, the path cannot close. The
maximum-support bound $q$ converts this exposure charge into a leaf count.
It is enough to bound the fresh support of offered questions, even if some
already fixed questions syntactically have a larger support.

## 3. Constants and an optimized corollary for the existing 3-CNF family

For the phase-16 family, take $r=3$, $\alpha=7/4$, $\beta=13/8$ and hence
$\delta=1/4$. A convenient conservative reserve is $R=8M$, where
$M=\max(1,w,b)$. Thus the earlier variable-tree bound extends to

\[
             2^{\max(0,\lfloor (s/8-M)/q\rfloor)}             \tag{6}
\]

leaves. Here $s=\lfloor10^{-16}n\rfloor$ in that asymptotic construction.
For fixed $w,b,q$ this is $2^{\Omega(n)}$. More generally the displayed
formula gives a quantitative support/width/scope tradeoff, without a bound
on arithmetic coefficient bit lengths.

The closure threshold need not be fixed at $13/8$. If $M<s/4$, put

\[
 \eta=\tfrac12\sqrt{M/s},\qquad
 \beta=\tfrac32+\eta,\qquad
 \delta=2\eta,\qquad
 R_* = M/\eta=2\sqrt{Ms}.
\]

Then $0<\eta<1/4$, so this $\beta$ is admissible. The real reserve $R_*$ is
at least one and at least each integer reserve in (1):
$2\lfloor w/\delta\rfloor\le w/\eta\le M/\eta$, and similarly for $b$.
Requiring the integer residual size to be at least this real value is
therefore sufficient; no unjustified rounding down of the reserve is used.
The same proof gives the stronger bound

\[
 \boxed{\quad 2^{\left\lfloor
       (\sqrt{s}/2-\sqrt M)^2/q\right\rfloor}\quad}           \tag{7}
\]

leaves, since

\[
 (\tfrac14-\eta)(s-M/\eta)
       =s/4-\sqrt{Ms}+M=(\sqrt{s}/2-\sqrt M)^2.
\]

For $M\ge s/4$ use the trivial one-leaf bound instead. At fixed $M$, the
exponent in (7) approaches $s/(4q)$ up to a sublinear loss; this is an
optimization of the same closure proof, not a different complexity result.
The tiny existential expansion constant still makes this an asymptotic
statement, not a useful numerical hardness prediction for small instances.

For example, fixed $w,b$ and $q=O(\log n)$ still require
$2^{\Omega(n/\log n)}$ leaves. Conversely, if $M=o(n)$ on this family,
any polynomial-leaf tree in the stated model must have maximum query support
$q=\Omega(n/\log n)$. To see the resource tradeoff directly, a tree with $L$
leaves and $M<s/4$ satisfies

\[
       (\sqrt{s}/2-\sqrt M)^2\le q(\log_2 L+1).
\]

These consequences concern a particular proof language, even though all its
arithmetic moduli and coefficient bit lengths are unrestricted.

The matching step also works for a query that returns
$c+\sum_{v\in Y}a_vx_v$ in an abelian group, with every displayed $a_v\ne0$:
flipping the reserved coordinate gives two distinct answers. A multiway tree
then has at least the same binary subtree and lower bound. This assertion
concerns the returned group value, not an arbitrary Boolean predicate of it.
It is a lower bound under sound context premises that disappear when all their
coordinates are assigned; the Gaussian context checker above is specifically
for $\mathbb F_2$, and no efficient checker for arbitrary group constraints is
claimed here.
Arbitrary bounded-support Boolean functions are **not** covered: fixing the
other coordinates can make such a function insensitive to the reserved bit.
For example, on the one-clause input $x\lor y\lor z$, asking that very OR
has three fresh coordinates but only answer one can be extended to a model.
The two-sided-offer step would be false for that query.

## 4. Why the theorem does not automatically cover arbitrary wide parities

If $q$ is linear in $n$, (6) or (7) can be trivial. The proof does not permit
replacing $q$ or $|A|$ by the rank of the queried parity equations.

There is a simple counterexample to that proposed proof modification. Take
$m\ge9$ proper ternary sunflower clauses, all sharing one pivot and each with
two private leaves. Signs can be arbitrary. Every nonempty subfamily $U$ has
$2|U|+1>7|U|/4$ neighbors. Ask the single parity of **all $2m$ private leaves**.
The query matrix has rank one. After adding its support to $A$, the maximal
closure for $\beta=13/8$ is all $m$ clauses, since the neighborhood outside
$A$ is just the shared pivot. Thus

\[
                  |C|=m\ge9>8\cdot\operatorname{rank}(P).
\]

The correct exposure inequality $|C|<8|A|$ still holds. Both parity answers
can be extended by the matching argument. This is a counterexample to the
**rank charge inside this construction**, not an UNSAT counterexample to every
possible arbitrary-parity lower bound. The sunflower itself is satisfiable.
The raw-clause-leaf parity-tree results reviewed in the prior-work note have
different terminal capabilities and do not erase this distinction.

## 5. Reproducible checks and remaining boundary

`python experiments/parity_localization.py --out-dir <directory>` writes
[`parity_localization.json`](../results/parity_localization.json). It uses the
same signed seven-petal satisfiable control as phase 18. It enumerates every
first parity support of size one through three and both answers, then checks
overlapping and adaptive follow-up queries, repeated/cancelled questions, and
questions forced by already absorbed coordinates. Every transition checks
maximal closure against all raw subsets, all applicable residual neighborhoods
and boundaries, Hall repair, preservation of every earlier answer, and the two
extensions differing in just the reserved bit. The nine-petal rank-one
counterexample is checked separately. The report records the exact coverage;
it does not claim to enumerate every possible query tree.

This is a reusable lower bound for a specified hybrid proof format. It neither
rules out all parity reasoning, nor handles sharing between incomparable
branches, nor gives a lower bound for every SAT algorithm. An extension to
arbitrary-support parity questions with these stronger arithmetic terminals
requires a new invariant or a carefully proved simulation. Established lower
bounds for other parity proof systems should be recorded as such, rather than
being silently transferred to this one. No P versus NP solution is claimed.
