# Simulating one round of clause learning and a global integer sum

**Theorem (degree, not unrestricted SAT time).** Start from a Boolean CNF.
First derive ordinary resolution clauses, using only lines of width at most
$w$. Then certify affine integer laws by enumerating the Boolean assignments
on at most $b$ original variables per law, using clauses from the first
stage (including its raw axioms). Finish with **one** checked integer linear
combination of those laws giving a contradiction. The weights, local moduli
and scopes need not agree and may depend on the input.

* For an exact final sum there is an ordinary polynomial-calculus (PC)
  refutation over the rationals of degree at most $\max(w+1,b,1)$.
* For a modular sum, let $m\ge2$ be its *final* modulus, and $R$ its
  unreduced integer right-hand side, with $m\nmid R$. For **every** prime
  $p$ for which $t=v_p(R)<v_p(m)$, set $D=p^t$. There is an ordinary PC
  refutation over $\mathbb F_p$ of degree at most $\max(w+1,b,D)$.
* In particular, a squarefree final modulus always permits $D=1$.
  For $m=4$ and residual 2, reduction of the linear rows modulo two
  loses the contradiction, but $D=2$ suffices by the digit argument below.

This is a simulation of the *combination*, not an extrapolation from
separate lower bounds for its two stages. It applies to an arbitrary
width-bounded resolution prefix, not just binary implication paths.
In fact each accepted proper path conclusion in the implemented format has
a width-at-most-three derivation. For a path from $u$ to $v$, erase literal
cycles. If $u=v$, reuse the start clause. Otherwise compose its binary
clauses to $\neg u\lor v$ at width two, then resolve with the start clause.
If the path visits $\neg u$, the prefix already yields the unit $\neg u$;
resolving it with the start clause gives the nonpivot context, which may
be weakened to the claimed result. The simple path has no intermediate
return to $u$, so the proper binary chain has no tautological prefix to
retain. Skipping repeated literals in the final clause cannot increase
width. A certificate that uses input axioms
without listing them in the prefix may count any such cited axiom of
width at most $b$ as a local premise instead. No extension-variable
axioms, arithmetic-to-clause feedback loops, semantic oracle for wide
premises, branching rule, or multiple nested integer rounds are admitted.

## 1. Rules and the simple field reduction

Number the integer leaves by $i$. Write $a_i$ for a vector supported on a
scope $S_i$ of size at most $b$, $r_i$ for a right-hand side, $d_i$ for a
local modulus (zero denotes exact equality), and $u_i$ for an integer
weight. For each leaf, clauses $C_{i,1},\ldots,C_{i,h_i}$ have been
proved and use only $S_i$. Every local Boolean model of these clauses must
satisfy $a_i\cdot x=r_i$ modulo $d_i$ (or exactly if $d_i=0$). Define
$A=\sum_i u_i a_i$ and $R=\sum_i u_i r_i$. The global rule requires

* if $m=0$: $u_i d_i=0$ for all $i$, $A=0$, and $R\ne0$;
* if $m\ge2$: $m\mid u_i d_i$ for all $i$, $A\equiv0\bmod m$
  coordinatewise, and $m\nmid R$.

These are the conditions used by the [integer checker](../src/pnp_lab/integer_hull.py).
In particular the integer affine form $L_i(x)=u_i(a_i\cdot x-r_i)$ is
zero (respectively divisible by $m$) at every local model of its cited
clauses. Partial bit assignments used by two leaves need not coincide.
Soundness comes from deriving each resulting polynomial from the same
original CNF.

Encode each proper clause $C$ by $f_C=0$, where $f_C$ is the product of
its literal-falsity factors: $1-x$ for a positive literal, $x$ for a
negative one. Work with ordinary polynomial calculus: linear
combinations and multiplication by a variable, with Boolean axioms
$x^2-x=0$. Degree counts the polynomial lines, *including products before
any reduction*. Duplicate literals are normalized and tautologies may be
discarded. The [width-to-degree construction](correlation_polynomial.md)
translates the prefix to any field in degree at most $w+1$. For a proper
resolvent, multiply each parent polynomial only by falsity factors
present in the other parent's nonpivot part but not its own; adding cancels
the pivot. Multiplication by $1-y$ uses one multiplication by $y$ and a
linear combination. Each intermediate uses only the resolvent variables
and its pivot. Weakening to a larger proper clause uses its missing factors.

**Local interpolation lemma.** Over any field, let $g$ be a multilinear
polynomial in variables $S$ and let it vanish on the Boolean models of
some cited clauses on $S$. For $\alpha\in\{0,1\}^{S}$ put
$\delta_\alpha=\prod_{\alpha_j=1} x_j\prod_{\alpha_j=0}(1-x_j)$.
If $g(\alpha)\ne0$, some cited clause $C$ is false at $\alpha$. Its
indicator $f_C$ divides $\delta_\alpha$: multiply the already proved
$f_C$ by the missing indicators, each on a fresh variable. This derives
$\delta_\alpha=0$ at degree at most $|S|$. Sum these lines with
coefficients $g(\alpha)$. The result is exactly $g$, since both sides of
$g=\sum_\alpha g(\alpha)\delta_\alpha$ are multilinear and agree on
every Boolean assignment. This uniqueness follows by splitting
successively on $x_j=0,1$, over *any* field. The zero function requires
no nonzero line. This lemma costs at most $O((b+1)2^b)$ PC lines per
local polynomial; the table enumeration also inspects the cited clauses.
It is an explicit derivation, not an additional semantic PC rule.

For $m=0$, each $L_i$ vanishes on the local models over $\mathbb Q$. Derive
it by interpolation and sum. The result is the nonzero constant $-R$;
scale it to 1. If $p\mid m$ and $p\nmid R$, the identical argument works
in $\mathbb F_p$. Such a prime always exists when $m$ is squarefree and
$m\nmid R$. It can exist for a nonsquarefree modulus as well. The relevant
test is whether an actual prime divisor detects the residual, not simply
whether the modulus has a repeated factor.

## 2. A higher digit covers prime powers

Now choose any $p$ with $t=v_p(R)<v_p(m)$; at least one exists by integer
factorization and $R\ne0$. The valuation $t$ is unchanged if the
certificate stores $R\bmod m$ instead of $R$. The following construction
can take the detecting prime as a parameter; it is an existence proof
about PC degree, not a polynomial-time factoring algorithm.

Work in the truncated series ring
$\mathbb F_p[z]/(z^{D+1})$, $D=p^t$. The symbol $z$ indexes a list of
coefficients; **no new proof variable or extension axiom is introduced**.
Integer powers $(1+z)^e$ are well-defined even for negative $e$, because
$1+z$ is a unit. Two elementary identities do the arithmetic:

1. If $p^{t+1}\mid e$, then $(1+z)^e=1$ in this ring. Indeed
   $(1+z)^{p^{t+1}}=1+z^{p^{t+1}}=1$ there; the same holds for its inverse.
2. If $e=p^t h$ with $p\nmid h$, then
   $(1+z)^e=(1+z^D)^h=1+h z^D$ there. Terms containing $(z^D)^2$ vanish,
   and $(1+z^D)^{-1}=1-z^D$, which also proves the formula for negative $h$.

For each leaf, form a polynomial-valued series
\[
 G_i(z,x)=(1+z)^{-u_i r_i}
   \prod_{v\in S_i}\left(1+x_v\big((1+z)^{u_i a_{iv}}-1\big)\right)
      =1+\sum_{j=1}^D g_{ij}(x)z^j .
\]
At a Boolean word this evaluates to $(1+z)^{L_i(x)}$. Every $g_{ij}$ is
multilinear, with degree at most $\min(j,|S_i|)$: each variable-bearing
factor costs at least one power of $z$. On a local model $L_i(x)$ is
divisible by $m$, hence by $p^{t+1}$. Identity 1 shows that all
$g_{ij}$, $j>0$, vanish there. Derive each nonzero $g_{ij}=0$ from its
cited clause polynomials by the interpolation lemma, at degree at most $b$.
The *derived line itself* has degree at most $j$ even when its local proof
contains lines of larger degree.

Let $E_{i,k}$ be the formal $z^k$ coefficient of
$G_1\cdots G_i$, with the empty product equal to 1. Compute in the
ordinary polynomial ring in $x$, keeping only the needed $z$ degrees.
Before any Boolean reduction, $\deg_x E_{i,k}\le k$, by addition of
degrees in products. The telescoping identity for a product minus 1 gives
\[
 [z^D]\prod_i G_i =
   \sum_i \sum_{j=1}^D E_{i-1,D-j}\, g_{ij}.
\]
The multipliers $E$ are not assumed proved. For any explicit monomial of
$E_{i-1,D-j}$, multiply the already derived $g_{ij}$ successively by
its variables, apply the monomial's scalar, and add. Every step has
formal degree at most $j+(D-j)=D$ even with repeated variables. This
derives the left-hand polynomial as a PC line. Computing the multipliers
can be expensive; it does not change the degree calculation.

Finally evaluate that polynomial at any Boolean $x$. Exponents add:
$\sum_i L_i(x)=A\cdot x-R$, with $p^{t+1}\mid A\cdot x$. By the two
identities its value is the same nonzero field constant
$-R/p^t\bmod p$, for every Boolean $x$. To recover this constant as an
ordinary PC line, multilinearize the derived polynomial one monomial at
a time: replace $M$ containing $x_v^2$ by $M/x_v$ using the Boolean axiom
multiplied by $M/x_v^2$. This costs degree $\deg M\le D$ throughout.
For $D=1$ there are no repetitions to reduce. The resulting multilinear
polynomial is the displayed constant by Boolean-cube uniqueness. Scale
to 1. This proves the bound without assuming a free high-degree
Boolean reduction or a high-degree multiplication shortcut.

For instance $m=4$, $R\equiv2\bmod4$ gives $p=2,t=1,D=2$.
Summing just the linear forms modulo two gives zero on both sides;
the coefficient of $z^2$ instead detects $-R/2\equiv1\bmod2$.
The example therefore separates the *linear reduction* from the digit
construction. It does not separate the underlying certificate from PC.

The [first-digit coefficient checks](../results/feedback_simulation.json) and
[higher-digit audit](../results/feedback_digits.json) are finite evidence.
The latter compares truncated powers (including negative exponents) with
generalized binomial coefficients, and verifies local and global polynomial
identities on the selected inputs. The first nonzero **series index** is not
a measured minimum PC degree. For related work on degrees of Boolean
functions modulo prime powers see [Sun, Sun, Wang, Wu, Xia, and Zheng, ICALP
2020](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2020.100).
We make no priority claim for the digit arithmetic or its use in complexity.

## 3. Size, field choice, and the actual obstruction

The degree bound is not a blanket polynomial size or bit-time bound.
For a prefix with $P$ lines, its arithmetic translation has $O((w+1)P)$
lines, with at most $2^{w+1}$ monomials per local product. For $H$ integer
leaves there are at most $HD$ nonconstant local coefficient polynomials,
each using the interpolation bound above; a local line has at most $2^b$
monomials. Polynomial multipliers for the telescoping step can have up to
$\binom{n+D}{D}$ monomials of degree at most $D$ in $n$ original variables,
including repeated powers. For example, derive each product in the double
sum with at most $O((D+1)\binom{n+D}{D})$ line operations and use at most
$O((D+1)^2\binom{n+D}{D})$ further multiplications/linear combinations for the
final multilinearization. Count separately the monomials actually written
on each line and the bit costs of their labels and field coefficients.
Ordinary dense polynomial arithmetic suffices. Truncated integer powers
can be computed by binary powering (and the finite inverse of $1+z$ for
negative exponents), so one need not expand a binary-encoded exponent into
that many repeated factors. For fixed $w,b,D$, and a supplied detecting
prime, this is polynomial in the encoded input **and the supplied source
certificate**, including all integer coefficient bit lengths. Finding
that certificate is another question. A varying $D$ may be enormous
relative to the bit length of $m$.

The [phase-16 hard family](correlation_proof_boundary.md#4-a-scalable-control-in-the-same-proper-linear-3-cnf-class)
has an ordinary PC degree lower bound $c n$ over **every** field with the
same constant $c>0$ (for sufficiently large $n$). This uses the
clause-variable unique-neighbor lower bound in
[Mikša–Nordström, Theorem 4.2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol033-ccc2015/LIPIcs.CCC.2015.467/LIPIcs.CCC.2015.467.pdf).
Characteristic-dependent lower bounds for specific counting formulas,
such as [Buss–Grigoriev–Impagliazzo–Pitassi](https://mathweb.ucsd.edu/~sbuss/ResearchWeb/lineargaps/journalfinal.pdf),
are a different statement: hardness over just one field would not justify
choosing a prime after seeing the solver's certificate.

Thus on that family an exact or squarefree certificate of this entire
type requires $\max(w+1,b,1)\ge cn$. More generally, for a fixed modular
certificate the inequality
\[
 \max\{w+1,b,\min_{p:\ v_p(R)<v_p(m)}p^{v_p(R)}\}\ \ge\ cn
\]
is necessary. The minimum is over detecting prime divisors of $m$.
If both scope measures stay small, **every** detecting characteristic
has a large digit index. Increasing the exponent in the modulus while
keeping a low nonzero residual digit does not evade this obstruction.
A large digit index is only a necessary condition: the bound supplies
no efficient certificate using it. This lower bound permits $D=\Theta(n)$, an index whose binary encoding
has only logarithmically many bits. It therefore does not give
a superpolynomial lower bound on the length of arbitrary integer
certificates.

**Next falsifiable question.** Does the bit cost of *finding* a certificate
with sufficiently high detecting digit stay polynomial on any family for
which all-field PC has large required degree, with the local scopes and
the prefix width held small? Specify the input coordinates, scopes, integer
weights and discovery cost; a big numerical modulus without a high
necessary digit is not evidence. Alternatively, identify an explicit rule
outside the one-prefix/one-sum model and analyze that rule. Neither this
simulation nor the known lower bound establishes P versus NP, or a limit
on all proof systems.
