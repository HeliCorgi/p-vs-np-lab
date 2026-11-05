# How much can variable branching buy on the expanding 3-CNF family?

On the [phase-16 neighborhood expanders](correlation_proof_boundary.md#4-a-scalable-control-in-the-same-proper-linear-3-cnf-class),
variable queries do not rescue a small-width, small-scope integer refuter
unless it grows a large **tree**. This result is specific to the following
model. Internal nodes query an original Boolean variable, with both values
as children. At a leaf the formula restricted by that path has a phase-17
refutation: ordinary resolution/weakening of width at most $w$, local
integer affine laws on at most $b$ remaining coordinates, and one final
weighted exact or modular contradiction. The prefix at each leaf can be a
DAG of arbitrary length, and each leaf can use its own moduli and weights.
There is no reuse of learned clauses or arithmetic between incomparable
branches. More general branching programs, arbitrary linear-form queries,
extension variables, and a Boolean-domain test on a derived arithmetic
row are outside the claim.

## One pin: even choosing the two arithmetic systems separately fails

Write $F|_\rho$ for deletion of satisfied clauses and false literals after
setting $u$ to one Boolean value. Each width-$w$ proof clause $C$ in
$F|_\rho$ can be lifted back to $C\lor \ell$, where $\ell$ is the literal
on $u$ *false* under $\rho$. Lift a surviving input clause by reusing its
source or weakening it with $\ell$; lift a resolution by using the same
pivot on the lifted parents. The extra literal appears with only one sign.
Width grows by at most one. A directly cited restricted input clause may
instead be lifted as a raw local premise (or weakened raw premise on the
same enlarged scope); its semantic support needs at most one original clause.

Take the union of the small raw supports of the lifted clauses for a leaf
scope $S$, as in the [localization proof](support_localization.md), now
within $S\cup\{u\}$. For the phase-16 family this applies when
$4(w+1),4(b+1)\le s$. Hall surplus two lets us match all clauses in this
union **avoiding both** $u$ and any specified free coordinate $v$. Set the
distinct matched variables to their satisfying literal values. Then set
$u$ as required and flip $v$ independently. This pair of models satisfies
every restricted learned clause on $S$. It follows that any affine law
on the free coordinates is an identity. If a proof also names the pinned
coordinate, substitute its prescribed Boolean value. Neither branch can
give a contradiction, even if its weights and characteristic are chosen
after the pin. The double-flip argument alone does not imply that *every*
assignment to two or more pins works: setting two literals of a ternary
clause false forces the third.

## Arbitrary adaptive variable queries: a leaf lower bound

Let $s\ge1$ and assume that every nonempty set $U$ of at most $s$ raw
proper ternary clauses satisfies $|N(U)|>7|U|/4$, as in the phase-16
construction. Put $M=\max(1,w,b)$ and $K=\max(0,\lfloor s/8\rfloor-M)$.
**Any finite refutation tree of the stated kind has at least $2^K$
leaves.** In particular the fixed-width, fixed-scope model needs
$2^{\Omega(n)}$ leaves on the UNSAT family for all sufficiently large
variable counts $n$. Its expansion constant is deliberately small, and
this is an asymptotic existence result, not a bound measured at 31 variables.

### Maintain a partial assignment with expansion left over

Let $A$ count only questions whose two answers the adversary offered.
Maintain a set $C$ of at most $s$ absorbed **raw clause IDs**, all satisfied
by a partial assignment on $X=A\cup N(C)$. Require

\[
    |N(C)\setminus A|\le \gamma |C|,\qquad \gamma=13/8,
\]

and take $C$ inclusion-maximal subject to this inequality and the size
bound, among supersets of the previously absorbed set. Initially both
sets are empty; strict raw expansion makes the empty set maximal at the
start. At every later step with $C\ne\varnothing$, the two neighborhood
bounds imply $|C|<8|A|$. The weak bound $|C|\le8|A|$ also holds when empty.

For any nonempty $U$ disjoint from $C$ with $|U|\le s-|C|$ we have

\[
               |N(U)\setminus X|>\gamma |U|.                 \tag{1}
\]

Indeed, the neighbors of $C\cup U$ outside $A$ consist of the old
neighbors of $C$ outside $A$ and the fresh neighbors of $U$ outside $X$.
Failure of (1) would make the strictly larger, still admissible $C\cup U$
eligible, contradicting maximality. This argument counts clause IDs,
not positions in a display of a proof.

If a queried variable is already in $X$, answer using its assigned value.
Nothing grows. For a fresh query $x$, put $A'=A\cup\{x\}$ and extend
$C$ to a maximal $C'$, still of size at most $s$, for $A'$. This is
possible: the old set remains eligible. Any subfamily $U\subseteq C'\setminus C$
lies within the size range in (1). Since $\gamma>1$, there are at least
$|U|+1$ fresh neighbors whenever $U$ is nonempty. Removing $x$ still
leaves Hall's condition. Match each newly absorbed clause to a distinct
variable *outside* $X\cup\{x\}$, and set it to satisfy that clause.
All old values may stay fixed, and either answer to $x$ now works. Fix
other newly included coordinates arbitrarily. This proves extension of the
state for each of the two answers. It is an existence strategy for a lower
bound; we do not charge it as a solver or assume that a maximal set can
be found efficiently.

### Why no leaf can close early

Restrict the original formula by the entire maintained assignment on $X$.
Absorbed clauses disappear. In any nonempty set of $t\le s-|C|$ surviving
clauses, the neighbors are exactly those original neighbors outside $X$.
Satisfied clauses may be discarded, so (1) holds for the survivors.
Duplicate residual clauses, if normalized, can use one representative
raw ID each. There are at most $3t$ incidences. Thus the number of
variables occurring in exactly one selected clause is at least
$2|N(U)\setminus X|-3t>t/4$. And (1) directly gives at least $t+1$
neighbors, enough for a matching after deleting any one free coordinate.
The [support localization argument](support_localization.md) therefore
applies to **affine** leaves on this residual: it needs boundary expansion
and Hall surplus one, not three literals in every surviving clause.
It rules out an integer contradiction whenever $8M\le s-|C|$.

This stronger restriction is legitimate even though the actual path
need not query every variable in $X$. Any leaf proof under the path
assignment would restrict further to one under the maintained assignment.
A satisfied clause is discarded; every surviving resolution line has
a derivable restricted subclause (when a pivot is set, use the surviving
parent, weakening if needed). This is the usual width-nonincreasing
restriction of resolution. For an arithmetic row $a_i\cdot y=r_i$
modulo $d_i$, subtract the fixed contributions from $r_i$. Its local
validity on the remaining coordinates follows by restoring the fixed
bits. The summed RHS changes by the fixed coordinates dotted with their
aggregate coefficients; these cancel exactly or are divisible by the
final modulus. Thus the contradiction survives with no increase of width
or scope. A satisfied local premise can be omitted.

While $|A|\le\lfloor s/8\rfloor-M$, the bound on $|C|$ ensures
$8M\le s-|C|$. For $K>0$, follow compatible branches up to the $K$th
freely answered question. No earlier leaf can close; forced questions
have one compatible successor and free questions have two. The tree is
finite, so this produces $2^K$ distinct prefixes after that question,
each with a different descendant leaf. Equivalently, split mass equally
on each free choice. A compatible leaf gets mass at most $2^{-K}$.
For $K=0$ the stated bound is the trivial one leaf. Depth alone would
not prove an exponential leaf count; it is the two-sided extension that does so.

### Evidence and limits

The [finite audit](../results/branch_localization.json) checks maximal
absorption, Hall repair for **both** replies, consistency of old values and
residual neighborhood expansion across shared and fresh queries on a small
signed sunflower. It does not test an exponentially large UNSAT tree.
The proof uses a maximal deficient-set construction in the tradition of
[expander closure arguments, §2.1](https://eccc.weizmann.ac.il/report/2021/076/revision/1/download)
and the classical [Prover–Delayer counting idea](https://eccc.weizmann.ac.il/report/2012/161/).
The role of localization here is to rule out a much stronger *terminal
certificate* than simply falsifying a raw clause. No priority is claimed
for the closure or counting devices. This theorem does not apply to all
possible refutation rules or to all deterministic algorithms for SAT.
