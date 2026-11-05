# Why the same field switch needs a branch in the one-sum model

The UNSAT input of [the Boolean field switch](../src/pnp_lab/field_split.py)
has two flow banks and one shared selector. Fixing the selector lets the
refuter use one short modular sum on each branch. **On the same expander
instances, without the split, no bounded-width resolution prefix followed
by bounded-scope affine integer laws and one global sum can refute them.**
Neither the final modulus nor the size of its detecting digit is restricted.
Here is a signed-integer witness for this assertion. It is different from
the [full-lattice proof](support_localization.md) for the phase-16 family:
some local laws on the switch really are nontrivial.

## Set-up and quantitative statement

Take a connected simple cubic graph $G$, subdivide one edge with a portal
vertex $t$, and call the resulting graph $H$, with $N$ vertices. Choose
an integer $k\ge3$ such that deleting **any** at most $k$ edges of $H$
leaves a connected component of size **strictly greater than** $N/2$.
The strict majority, hence uniqueness, is used below. For a family of
edge expanders one can take $k=\Omega(N)$. Indeed, if $G$ has edge
expansion $h>0$ on shores up to half its vertices, any cut of $H$ with
both shores of size at least $N/4$ has at least $h(N/4-1)$ crossing
edges: delete $t$ from the shores and use that subdividing an edge crossing
the original cut cannot remove its crossing. If no component after
deletion is a majority, either a component already has size in
$[N/4,N/2]$, or summing components of size below $N/4$ gives such a
shore. Every crossing edge of that cut was deleted. Thus
$k<h(N/4-1)$ suffices for large $N$. This is not an expansion claim for
the small prism or clique controls.

Use the UNSAT charges in `switch_flow`, and the literal encoding in
[`_encode`](../src/pnp_lab/ternary_flow.py). With divergence defined
by outgoing minus incoming edge value, the binary bank demands charge
one at vertex 0 and the ternary bank has zero base charges. Both banks
add the Boolean selector $\sigma$ to the demand at $t$. For $\sigma=0$,
the binary demand totals one mod 2, and the ternary bank is consistent.
For $\sigma=1$, the binary demand totals zero mod 2, but the ternary bank
totals one mod 3. Connected-graph incidence equations are solvable for
any total-zero demand over either field: assign a spanning tree from the
leaves upward, taking all non-tree values zero. Conversely, summing all
vertex equations always gives zero on the edge side. Thus neither selector
value permits a global Boolean model.

**Theorem.** For $w+1\le k$ and $b\le k$, consider any width-$w$ ordinary
resolution and weakening prefix on the original Boolean variables. Then
consider all integer affine equalities and congruences each valid from
raw or prefix clauses wholly inside a scope of at most $b$ Boolean
variables. There exists a **single global integer vector** satisfying
all those laws, so they cannot yield a contradiction by any one weighted
sum of the [phase-17 form](feedback_simulation.md). For sufficiently
large expanders, $w$ or $b$ must consequently be linear in graph size.
The assertion is about unconditioned rules. The two separately checked
conditional contradictions use a different proof rule and escape it.

## 1. Nonnegative, consistent local views of one inconsistent bank

Fix a selector value. Call $q\in\{2,3\}$ the active inconsistent field;
the other bank is set to one actual solution at that selector throughout.
Let $d$ be the prescribed active demands, of total $1$ in $\mathbb F_q$.
For an exposed set $X$ of at most $k$ active **edges**, let $B_X$ be the
majority component of $H-X$. Pick any $r\in B_X$. Correct $d$ by
subtracting its total at $r$. The corrected global system is nonempty;
take a **uniform** solution and retain only its edge values on $X$.

The distribution so obtained does not depend on $r$. For $r,r'\in B_X$
there is a path from $r$ to $r'$ avoiding every exposed edge. Adding a
suitably oriented unit path flow moves the correction from $r$ to $r'$,
giving a bijection of solution sets that is the identity on $X$. Also, for
$X\subseteq Y$, $B_Y\subseteq B_X$: its containing component in $H-X$
is still a strict majority. One can use the same correcting vertex of
$B_Y$ for both and take ordinary marginals of the same uniform global
solution distribution. The views on $Y$ therefore project to the views on
$X$. The projected distribution is uniform on the image of a nonempty
affine space under coordinate projection (all fibers have the same size).
Its point masses are zero or $q^{-d_X}$ with $d_X\le|X|\le k$.

For a set $S$ of at most $k$ **Boolean variables**, expose in the active
bank the distinct edges named by members of $S$. There are at most $|S|$
of them. In the binary bank an edge value is one bit; in the ternary bank
its indicators are deterministic functions of one field element. Push the
edge view through these functions. Insert the fixed selector and the fixed
consistent-bank bits wherever $S$ requests them. Call the result $P^q_S$;
it is a normalized nonnegative rational distribution. These tables
marginalize consistently for every inclusion of Boolean scopes, even if
dropping one ternary indicator does not drop its underlying edge.
Although indicators can merge several field assignments, every Boolean
mass still has denominator dividing $q^k$.

Every raw clause has zero mass on its forbidden words. To check this against
the actual encoding:

- The ternary domain clauses (one positive triple and three negative
  pairs per edge) hold identically on an indicator encoding.
- A regular vertex clause checks a tuple by mentioning a bit or selected
  indicator for **each** incident edge. When its whole scope is exposed,
  all those edges are removed from $H$ for the majority-component test.
  The vertex is isolated, so cannot be the correction vertex. Its original
  vertex equation is satisfied.
- Each portal clause similarly mentions both incident edges and the bit
  $\sigma$. Its forbidden tuple uses that particular value of $\sigma$.
  The active portal, when exposed, is isolated, so the equation there
  is satisfied for the selector value used in this view. The frozen bank
  satisfies all its own clauses.

The argument survives a signed renaming of the Boolean coordinates by
permuting/complementing the local tables.

## 2. Propagate support first; combine signs only afterwards

For **each** of the two ensembles separately, any positive-mass assignment
on the variables of a width-$w$ derived clause satisfies it. This follows
inductively. For a proper resolution step the parents' variable union
has size at most $w+1$: it consists of the resolvent's coordinates plus
its pivot. Every positive word on the resolvent has a positive extension
on that union by marginal consistency, and both parent restrictions then
have positive mass by nonnegativity. Those restrictions jointly satisfy
the parents, hence the resolvent. Weakening and raw axioms obey the same
support assertion. For any scope $S$ up to size $b$, a positive word
therefore satisfies all cited clauses contained in $S$ simultaneously.
The support induction here is not an inference from a signed zero mass;
signed masses could cancel in a marginal.

Since $2^k,3^k$ are coprime, choose integers $A,B$ with
$A2^k+B3^k=1$. For every Boolean scope $S$ up to size $k$ define

\[
              M_S(\alpha)=A\,2^k P^2_S(\alpha)
                             +B\,3^k P^3_S(\alpha).
\]

These numbers are integers; their sum is one; and they project
consistently. Any assignment violating a cited clause has value zero in
both component tables, hence value zero in $M_S$. Negative entries really
occur: the two masses on the selector singleton are the nonzero integers
$A2^k$ and $B3^k$, both of absolute value at least two and summing to one.
These $M$ are not probabilities or actual models.

For each Boolean coordinate $j$ put $y_j=M_{\{j\}}(1)\in\mathbb Z$.
Given any certified local row $a\cdot x=r\bmod d$ on $S$, sum
$M_S(\alpha)(a\cdot\alpha-r)$ over all $\alpha$. Every nonzero summand
is divisible by $d$; for $d=0$ it vanishes exactly. By projection and
normalization this sum is $a\cdot y-r$. This proves that the **same** $y$
obeys every such row, for any $d$, independent of which ensemble or scope
would best detect the row. No sound integer linear combination can
contradict a common integer solution.

The same construction assigns consistent integer moments
$y_T=M_T(\text{all ones})$ to every squarefree monomial on $|T|\le k$,
with $y_\varnothing=1$. Thus sums of local polynomial laws treated
**linearly in these moment coordinates** also have a common integer
solution. In general $y_{\{i,j\}}\ne y_i y_j$; no multiplicative
substitution into an unrestricted nonlinear proof system is justified.
Nor does a signed combination preserve inequalities. In this construction
$y_\sigma=B3^k$ is outside the Boolean interval. A rule insisting
on an actual Boolean selector, or splitting on its two possible
values, cannot be refuted by this signed vector.

These are existential tables. Enumerating all of them at a level linear
in $N$ is not presented as an efficient SAT algorithm. The field switch,
unlike the Hall family, has real linear/congruence information locally;
the obstruction is that the unconditioned information has a common
signed-integral realization. It applies even after an arbitrary number
of narrow resolution lines, not just a particular path heuristic.

## 3. Relation to earlier results

The combination of coprime denominator solutions by an integer Bézout
identity, and an OR construction involving two Tseitin characteristics,
are already central to [Lichter and Pago, ICALP 2025, revised version
§§4–5](https://arxiv.org/html/2407.09097v3). Their results concern
broader CSP algorithms; no novelty claim is made for the arithmetic
gluing principle or for leveraging different characteristics.
[Conneryd, Ghannane and Pang, SODA 2026, §1.3 footnote 2](https://arxiv.org/html/2511.17272v1)
also explicitly explain how the earlier disjunction gives a family
with large PC degree over every field by restrictions. Such a
fixed-field PC bound alone would not exclude an arbitrary large final
integer modulus. The role of the proof here is to verify the uniform
flow marginals and coprime gluing directly for this repository's raw
Boolean portal/indicator clauses **after narrow resolution learning**.
Together with the positive split proof, it separates those two specified
proof formats on the *same* formulas, not P from NP.
