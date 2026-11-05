# Parity branching with polynomial-calculus leaves: an exact degree bound

This note supplies a reusable lower-bound transfer for **one common field,
F2**. It allows arbitrarily wide parity questions and arbitrary DAG
polynomial-calculus proofs at the leaves. It does not allow changing the
field from leaf to leaf. The argument is an elementary deduction-and-tree
balancing synthesis; no priority is claimed for the underlying method or
for exponential parity-tree lower bounds already in the literature.

The statements below are mathematical proofs.
[Formal/ParityQueries.lean](../Formal/ParityQueries.lean), declaration
`degree_rank_mass`, formalizes the abstract rank/counting inequality.
That statement is not a formal verification of the PC deduction lemma or
the full simulation.

The [finite ordinary-PC audit](parity_pc_audit.md) constructs and
independently replays explicit deduction and tree-gluing traces; its
[reproduction script](../experiments/parity_pc.py) and
[recorded report](../results/parity_pc.json) exercise raw-clause leaves
and general conditional PC traces. They do not implement the full
arithmetic-leaf interface of Section 6.

## 1. Model and theorem

Let F be a finite set of polynomials in `F2[x₁,…,xₙ]`, interpreted as
zero equations, and include the Boolean equations `xᵢ²−xᵢ=0`.
**Ordinary polynomial calculus (PC)** derives linear combinations of
previous lines and products of a previous line by one variable. Degree is
the maximum **formal polynomial degree of every intermediate line**.
There is no free Boolean reduction and no extension variable.

A finite binary tree queries affine F2 forms. The path to a leaf λ supplies
a set `P_λ` of affine equations with their chosen answers. At λ, require an
actual ordinary-PC refutation of `F∪P_λ`, of degree at most the integer
`d_λ≥2`. Only axioms actually used in that trace have to fit its degree
budget; unused polynomials in F need not have degree at most `d_λ`. Each
leaf may use its own PC DAG, with
unrestricted length and coefficient sharing inside that DAG. Refutations
at different leaves are not taken as unconditional extra axioms.

Write `D_PC(F)` for the minimum ordinary-PC refutation degree of F.

**Theorem, heterogeneous form.** Every such tree satisfies

\[
                 \boxed{\quad
                 \sum_{\lambda\text{ leaf}}2^{d_\lambda}
                     \ \ge\ 2^{D_{\rm PC}(F)}.
                 \quad}                                    \tag{1}
\]

More precisely, give a leaf the integer rank `d_λ`. If the two child ranks
are u and v, define the parent rank by

\[
 R(u,v)=
 \begin{cases}
 u+1,&u=v,\\
 \max(u,v),&u\ne v.
 \end{cases}                                                \tag{2}
\]

Then F has an ordinary-PC refutation of degree at most the root rank.
The weighted bound (1) is a consequence, not an assumption about a
probability distribution.

**Uniform form.** If every leaf has degree at most a common d, and the
tree has L leaves, then

\[
       D_{\rm PC}(F)\le d+\lfloor\log_2 L\rfloor,
       \qquad
       L\ge 2^{\max\{0,D_{\rm PC}(F)-d\}}.                 \tag{3}
\]

In particular, a family requiring ordinary PC degree at least `c n` over
F2 has `2^{Ω(n)}` leaves whenever `d=o(n)`; more generally the displayed
bound charges the exact difference `D_PC(F)−d`. A parity involving all n
variables is still degree one here. The conclusion is therefore
independent of query-support size.

## 2. Discharging one affine assumption

Let P be any common set of affine path assumptions. Suppose

\[
                   F\cup P\cup\{a=0\}\vdash_{\rm PC}1
\]

through degree t, where `t≥2` and `a=ℓ−b` is an affine polynomial over F2.
Put `h=1−a`. We will derive h from `F∪P` through degree at most `t+1`.

Transform every line p of the original proof into hp. Check each rule:

1. **Axiom from F, P, or the Boolean equations.** Starting with p, derive
   `hp` by multiplying p separately by each variable occurring in h and
   adding the resulting polynomials and the possible constant multiple of
   p. Every one of these intermediate lines has degree at most `deg p+1`.
   Multiplication by a linear polynomial is thereby expanded into legal
   ordinary-PC steps.
2. **The discharged axiom a.** Its image is `a(1−a)`. Since the field and
   all affine coefficients are F2,

   \[
      a^2-a=\sum_{i:\,x_i\text{ occurs in }a}(x_i^2-x_i).
   \]

   Cross terms cancel and the constant is idempotent. This identity
   derives the required image from Boolean equations through degree two;
   signs coincide in characteristic two. It is a derivation of a formal
   polynomial, not a free quotient-ring reduction.
3. **Linear combination.** From `p=αu+βv`, use `hp=αhu+βhv`.
4. **Variable multiplication.** From `p=x_i u`, derive `hp=x_i(hu)`.
   Its formal degree is at most `deg p+1≤t+1`. Possible cancellations
   only reduce this bound; none is needed to hide an intermediate degree.

The last transformed line is `h·1=h`. If a transformed polynomial is
zero it can be omitted or obtained as a zero linear combination, as in
ordinary PC. All uses of a have been removed. This proves the deduction
lemma.

The equation `h=0` is exactly the opposite answer to the same parity:
`ℓ=1−b`. Thus a refutation of the opposite branch can now be appended,
using the derived h in place of its branch axiom. If the first branch has
refutation degree u and the other has degree v, the resulting degree is
at most

\[
                          \max(u+1,v).                       \tag{4}
\]

The Boolean degree-two derivation is already covered because `u≥2`.
No number of variables in ℓ occurs in (4).

## 3. Tree balancing and the weighted inequality

Apply the deduction lemma inductively at every node, keeping all its
ancestor equations as the common context P. If the child ranks differ,
discharge the smaller-rank child first. Integers `u<v` satisfy `u+1≤v`,
so (4) is at most v. If the ranks agree, either order costs one extra
degree. This is precisely (2). At the root P is empty.

For every subtree T define its weight

\[
                       W(T)=\sum_{\lambda\in T}2^{d_\lambda}.
\]

Induction gives `2^{rank(T)}≤W(T)`. At a leaf it is equality. At unequal
child ranks the larger child's weight already bounds the parent. At equal
rank r, the two weights sum to at least `2^r+2^r=2^{r+1}`. Since the root
rank is at least `D_PC(F)`, (1) follows.

For a uniform budget d, rank is `d+s(T)`, where s is the usual binary
branching/Strahler rank with leaf rank zero. The same induction gives
`2^{s(T)}≤L`, hence `s(T)≤floor(log₂L)` and (3). Alternatively, always
discharge the child with fewer leaves first: its leaf count is at most
`L/2`, giving the same bound. Tree depth alone does not give (3).

## 4. Raw-clause leaves are a special case

Let F be the ordinary clause-polynomial encoding of a k-CNF. Suppose a
path's affine equations imply that some raw clause C is false. If the
path system is inconsistent, Gaussian elimination derives one at degree
one. Otherwise it implies the falsifying bit value of every variable in C.
Each corresponding affine equation is a linear combination of the path
equations, again derivable at degree one.

Write the false-literal factors of C as `f₁,…,f_r`, with `r≤k` and each
factor either `x_i` or `1−x_i`. The path derives `f_j−1=0` for every j.
The identities

\[
 \prod_{j=1}^{r} f_j-1
   =\sum_{j=1}^{r}
       \left(\prod_{i<j}f_i\right)(f_j-1)
\]

give an ordinary-PC derivation of `f_C−1` through degree at most r: expand
multiplication by `1−x_i` into a subtraction and a variable multiplication.
Together with the input axiom `f_C=0`, this derives one. An empty input
clause already has polynomial one.

Thus a raw-clause parity tree has leaf degree at most `max(k,2)`, and

\[
        L\ge 2^{\max\{0,D_{\rm PC}(F)-\max(k,2)\}}.        \tag{5}
\]

This recovers the known exponential phenomenon by a direct argument with
explicit degree conventions. Applying it to the
[phase-16 expanding 3-CNF family](correlation_proof_boundary.md#4-a-scalable-control-in-the-same-proper-linear-3-cnf-class)
gives an exponential leaf bound for arbitrary parities. It is not a new
claim of priority over the prior PC/tree-size connections.

## 5. Low-degree completeness for an affine path context

**Lemma.** Let P be any affine system over F2 on the original Boolean
variables. If a formal polynomial q of degree at most e vanishes on
every Boolean solution of P, then P and the Boolean axioms derive q in
ordinary PC through degree at most `max(e,2)`. There is no restriction on
the support or number of equations in P, and no proof-size assertion.

If P is inconsistent, Gaussian elimination derives one using only linear
combinations. Multiply that line by the monomials of q and add; the
degree is at most `max(e,1)`. Otherwise, Gaussian elimination derives
reduced pivot equations `x_i−L_i(y)=0`, where y are the free variables
and each L_i is affine over F2. Substitute these expressions for the
pivots in q, obtaining `q_sub(y)` of degree at most e. The formal
difference `q−q_sub` is derivable through degree e. Indeed, telescope
the substitutions one pivot at a time and use

\[
 x_i^r-L_i^r=(x_i-L_i)
       \sum_{t=0}^{r-1}x_i^{r-1-t}L_i^t .
\]

In each affected monomial the multiplier of `x_i−L_i` has degree at
most e−1. Expand that multiplier into monomials and derive each product
by successive variable multiplications. Affine substitution never
increases degree, so this is an ordinary-PC derivation with the stated
intermediate-degree bound, including repeated powers.

Every Boolean setting of y extends to a Boolean solution of P: each
affine L_i takes values in F2. Thus `q_sub` vanishes on the entire free
Boolean cube. Reduce its monomials by the free-variable Boolean axioms,
without increasing their formal degree. The resulting multilinear
polynomial is zero, since a multilinear polynomial representing the zero
function on the Boolean cube has all coefficients zero. Combining this
derivation with `q−q_sub` derives q. Degree two covers Boolean axioms;
if e<2 no such reduction is necessary. This proves the lemma using legal
PC steps, rather than adding a semantic rule to PC.

Two useful instances are:

* A clause C implied by P has its falsity polynomial derivable through
  degree `max(|C|,2)`. This remains true when C follows from a linear
  combination of many path equations.
* If a local word α on a scope S has no extension satisfying P, its
  indicator `δ_α=∏_{α_i=1}x_i∏_{α_i=0}(1−x_i)` is derivable through
  degree `max(|S|,2)`. P can have arbitrarily wide equations; only the
  degree of this indicator is charged.

## 6. Conditional integer leaves with a common characteristic-two detector

The next corollary verifies a particular interface for the generic
theorem. Here F is a **proper CNF**: a raw clause has distinct variables
and no complementary pair of literals. Prefix and cited clauses use the
same normalized convention. This ensures that a false-clause polynomial
divides the corresponding Boolean-word indicator without repeated
factors. The phase-16 hard family is already proper. The generic theorem
of Section 1 still allows arbitrary polynomial input axioms.

At each leaf let P be its entire affine path context and allow the
following certificate, in the original variables:

1. A resolution/weakening prefix of width at most w, from F and from
   proper clauses actually implied by P. Directly cited raw clauses on a
   local scope may instead be charged to that scope.
2. Integer affine rows `a_i·x=r_i (mod m_i)`, with `m_i=0` denoting exact
   equality. A **local row** has scope S_i of size at most b and cites
   prefix/raw clauses on S_i. It must hold for every word on S_i that
   satisfies those clauses and extends to a solution of P. A **path
   row** may have arbitrary support but must hold on every solution of
   P, with its stated integer modulus or exact equality. In particular,
   a queried parity is a path row modulo two. Merely being a consequence
   of F is not a license to introduce a wide path row.
3. One weighted integer sum. Write `A=Σ_i u_i a_i` and `R=Σ_i u_i r_i`,
   for integer weights u_i. For a final modulus m≥2 require
   `m | u_i m_i` for every i, `A≡0 (mod m)` coordinatewise, and
   `v₂(R)<v₂(m)`. For an exact final sum require `u_i m_i=0` for all i,
   `A=0`, and `R≠0`.

For either final sum set `D=2^{v₂(R)}`. The modular condition is stronger
than merely requiring an even modulus and a nonzero residual: for
`m=6, R=2`, only characteristic three detects the contradiction, so
this corollary does not apply. Local moduli need not all be powers of
two, or even have a common prime factor. Their compatibility with the
final weighted sum is the relevant condition.

**Conditional simulation corollary.** Such a leaf has an ordinary-PC
refutation from `F∪P` over F2 of degree at most

\[
                  d=\max\{2,w+1,b,D\}.                    \tag{6}
\]

Here all semantic requirements on clauses and rows are hypotheses that
must actually be verified; the result does not declare an unimplemented
wide-row semantic oracle to be a polynomial-time checker. The proof below
constructs PC derivations once these requirements hold. The finite PC
converter linked below presently implements the generic PC-leaf bridge
and raw leaves, not this full arithmetic interface.

**Proof.** If P is inconsistent, derive one by Gaussian elimination.
Otherwise the preceding lemma derives every context clause used in the
prefix at degree at most `max(w,2)`. Ordinary resolution and weakening
simulate at degree at most w+1, as in
[phase 17](feedback_simulation.md#1-rules-and-the-simple-field-reduction).
A directly cited raw clause on S_i is already an axiom of degree at most
b. Thus all used clause polynomials are available at cost
`max(2,w+1,b)`.

Use the [phase-17 generating series](feedback_simulation.md#2-a-higher-digit-covers-prime-powers)
in `F2[z]/(z^{D+1})`, with z only a coefficient index, not a proof
variable:

\[
 G_i(z,x)=(1+z)^{-u_i r_i}
    \prod_{v\in\operatorname{supp}(a_i)}
       \left(1+x_v((1+z)^{u_i a_{iv}}-1)\right)
      =1+\sum_{j=1}^{D}g_{ij}(x)z^j.
\]

Every g_ij is multilinear and has formal degree at most j, regardless of
the row's support. On a Boolean word, G_i equals
`(1+z)^{u_i(a_i·x−r_i)}`. At a valid row model the exponent is divisible
by m in the modular case and is zero in the exact case. Its coefficients
through D therefore vanish: in the modular case
`2^{v₂(R)+1}` divides that exponent, and in this truncated ring the
corresponding power of `1+z` is one. Negative integer exponents cause no
problem because `1+z` is a unit.

For a local row, interpolate g_ij on S_i. If `g_ij(α)≠0`, then α either
falsifies a cited clause or has no extension satisfying P. In the first
case its indicator δ_α is a multiple of that clause's falsity polynomial;
multiply by the missing, fresh-variable indicators to derive δ_α
through degree at most b. In the second case apply the affine-context
lemma, at degree at most `max(b,2)`. Summing these lines with coefficients
`g_ij(α)` gives exactly g_ij by multilinear interpolation. For an
arbitrary-support path row, g_ij vanishes on all P-models, so the same
lemma derives it directly through degree `max(j,2)`. This justifies the
integer interpretation of wide path rows coefficient by coefficient;
no high-digit polynomial is assumed to be a linear path axiom.

Let E_{i−1,D−j} be the formal z^{D−j} coefficient of the preceding
product of G factors. Before Boolean reduction it has degree at most
D−j. The telescoping identity gives

\[
  [z^D]\prod_i G_i
       =\sum_i\sum_{j=1}^{D} E_{i-1,D-j}\,g_{ij}.
\]

Multiply each **already derived line** g_ij by the monomials of its
multiplier and sum. Every new intermediate has unreduced formal degree
at most `j+(D−j)=D`. A degree-b interpolation derivation of g_ij is an
earlier prefix; it is not itself multiplied by E. Its cost is therefore
combined by a maximum, not by adding b to D. This distinction is essential
and differs from the whole-trace transformation in the deduction lemma.

On every Boolean word, the resulting coefficient equals
`−R/2^{v₂(R)}=1` in F2: aggregate coefficients cancel modulo m, or exactly,
and this is the first nonzero coefficient of `(1+z)^{−R}`. The derived
formal polynomial has degree at most D. Reduce repeated powers using
Boolean axioms at degree at most D; Boolean-cube uniqueness makes its
multilinear remainder the constant one. For D=1 no powers need reduction.
Together with the costs already recorded, this proves (6).

Exact sums are included here using their characteristic-two detecting
digit. An exact sum with even R cannot simply use the degree-one rational
reduction from phase 17 as an F2 proof; D is charged explicitly and may be
large relative to the binary length of R.

Consequently, if each leaf λ has this interface with its own parameters,
then

\[
 \sum_{\lambda}2^{\max\{2,w_\lambda+1,b_\lambda,D_\lambda\}}
           \ge 2^{D_{\rm PC,\mathbb F_2}(F)}.              \tag{7}
\]

For common bounds w,b,D, equation (3) holds with d from (6). On the
phase-16 family this gives exponentially many leaves when
`max(w,b,D)=o(n)`, **even for arbitrary-support parity queries**. The
earlier [bounded-support localization theorem](parity_localization.md)
has a different strength: it allows arbitrary detecting characteristics
and digit indices, while charging the query support. Neither subsumes
the other in full.

The theorem does **not** combine F2 proofs on one branch with F3 proofs on
another. The switched-family example in
[phase 18](field_split_boundary.md) has low-cost mixed-characteristic
leaves despite large PC degree in every single field; it supplies no
common-F2 leaf degree bound and is not a counterexample to (1) or (7).

## 7. Scope, cost, and attribution

The output is a **degree upper bound** used contrapositively for a lower
bound. It is not a polynomial-time search algorithm for the output proof,
nor a polynomial bound on its sparse-monomial size. Discharging a wide
parity multiplies polynomials by a wide linear form; repeated expansions
can create many monomials even though the maximum degree has the stated
bound. This is why (3) must not be advertised as an efficient all-input
SAT procedure or as a size-preserving PC simulation.

The statement allows arbitrary PC DAGs inside a leaf, but the outer
conditional structure is a tree. Reusing a conditional derivation under
multiple incoming contexts requires a new soundness and degree argument;
there is no automatic extension to arbitrary parity decision DAGs.

For related established results, see
[Part–Tzameret, Section 9, Theorems 43–44](https://www.doc.ic.ac.uk/~itzamere/Res-Lin-Two.pdf)
on tree-like linear resolution size, width and PC degree, and the
[phase-19 primary-source map](parity_query_prior_work.md). The deduction
lemma above and the weighted form were written out here to fix the exact
leaf interface, characteristic and intermediate-degree charges. This is
an independently checked synthesis of standard algebraic proof techniques,
not a claim that a new general parity-tree lower-bound method has been
invented. Neither the published connections nor this synthesis covers
all deterministic algorithms for SAT.
