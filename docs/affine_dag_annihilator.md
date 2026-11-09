# A common-annihilator lower bound for affine-clause DAGs

**Phase 20 status (2026-11-08 JST): the stated F2 exponential application is
formalized, including the CNF family, separator and counting estimates.**
See [the exact theorem and verification record](phase20_formalization.md).
The paper argument below was reviewed within this research cycle; external
peer review and priority assessment remain separate. This proof-system lower
bound does not resolve P versus NP. Other applications still have to supply
the separated polynomial space required by the generic theorem.

The question arose while auditing the separated-space criterion in
[Braun's 2026 preprint](https://arxiv.org/abs/2609.23015v2) and its
[pinned formal source](https://github.com/kbr-/math-research/blob/25239211058ef718402a908b3272f01480c159c4/formalization/claims/GenericCNFSubspaceCriterion.lean).
That criterion motivated looking for a large space, rather than only a
refutation-degree lower bound. The proof given here works directly with the
falsity indicators of proof lines and a polynomial that vanishes on their
high-rank falsity flats. Its verification does not require the preprint's
bit-PHP theorem, ENS registry, or family-removal theorem. See the separate
[bounded source audit](braun_generic_audit.md) for what was actually read.

**Phase-23 formalization follow-up:** [optimal affine coordinates](optimal_affine_parameters.md)
are now constructed from every nonempty clause zero-set, and the actual
restriction budget uses `n-spanRank C`. The connected source-DAG Lean theorem
constructs all charts and covers internally, summing over nonempty discarded
node occurrences. Distinct-flat deduplication, the expander-separated source
space, and quantitative existence/counting remain separate formal obligations.
This update does not reclassify the entire paper theorem as Lean-verified.

## 1. Definitions and the exact statement

Work over $K=\mathbb F_2$ in the **ordinary** polynomial ring
$K[x_1,\ldots,x_n]$. The equations $x_i^2-x_i=0$ are explicit axioms.
Polynomial calculus (PC) permits the zero line, an input axiom, linear combinations, and
multiplication of a previously derived polynomial by one variable. The
degree of a derivation is the greatest ordinary total degree of any line.
There is no implicit quotient reduction during a derivation.
The zero line is trivially available at every degree, including zero.
This pins the convention used in the degree-zero cases below and in the
executable ordinary-PC checker; it adds no nonzero consequence.

Let $F$ be a CNF whose clauses are proper: every clause has distinct
variables and contains no complementary pair. Let its maximum width be $w$.
Write $\mathcal F$ for the ordinary falsity polynomials of its clauses,
together with all Boolean axioms. Define

\[
 C_B(F)=\{p:\ p\text{ has an ordinary-PC derivation from }\mathcal F
                   \text{ through degree }B\}.
\]

This is a linear subspace. Write $P_{\le k}$ for the space of ordinary
polynomials of total degree at most $k$, and put

\[
                 b_k(t)=\sum_{j=0}^{\min(k,t)}\binom tj
                 \qquad(t,k\ge0).
\]

An **affine clause** $A$ is a disjunction of conditions $g(x)=1$, where
each $g$ is an affine form over $\mathbb F_2$ on the original $n$ variables.
Its falsity set is

\[
                  Z(A)=\{x\in\mathbb F_2^n:\ g(x)=0
                                     \text{ for every }g\in A\}.
\]

If this set is nonempty, it is an affine flat. Its codimension $r(A)$ is
the dimension of the linear span of the affine forms in $A$. Equivalently,
after Gaussian elimination it is the number of independent equations
defining $Z(A)$. When the span contains the constant $1$, the clause is a
tautology and $Z(A)$ is empty; treat such a line separately, with indicator
$q_A=0$. The empty clause has $Z(A)=\mathbb F_2^n$, rank zero, and
indicator $q_A=1$.

A proof is a finite DAG of $S$ affine clauses, topologically ordered. Its
initial lines are the actual clauses of $F$. Each other line is a semantic
consequence of one or two earlier lines, and its final line is the empty
clause. Parents can be reused without restriction. This includes ordinary
resolution over parities and semantic weakening, and also permits any
sound binary semantic inference between affine clauses.

Fix integers $k\ge0$ and $w\le R<n$. A line is **high** when its falsity set
is nonempty and $r(A)>R$. Let $\mathcal Z$ be the set of **distinct**
falsity flats of the high lines. Every other line is low.

### Theorem 1: rank-profile dimension inequality

For every linear subspace $U\subseteq P_{\le k}$, set $B=k+3R$. Then

\[
\boxed{
 \dim U\ \le\
 \dim\bigl(U\cap C_B(F)\bigr)
       +\sum_{Z\in\mathcal Z} b_k(\dim Z).
}
\tag{1}
\]

In particular, if $U$ is separated from degree-$B$ consequences,

\[
                        U\cap C_B(F)=\{0\},
\tag{2}
\]

then

\[
\boxed{
 \dim U
    \le \sum_{Z\in\mathcal Z}b_k(\dim Z)
    \le |\mathcal Z|\,b_k(n-R-1)
    \le S\,b_k(n-R-1).
}
\tag{3}
\]

Thus

\[
              S\ \ge\ \frac{\dim U}{b_k(n-R-1)}.
\tag{4}
\]

The same ratio lower-bounds the number of **distinct high falsity flats**.
Repeated occurrences of an equivalent clause do not help meet the
dimension requirement. Formula (1) is more precise than the uniform
estimate: an individual line of still higher rank contributes a smaller
restriction space.

The theorem counts source proof lines. It does not assert that the
ordinary-PC simulation used in its proof has polynomial expanded size,
or that the separating space can be found efficiently.

## 2. Two ordinary-PC facts with explicit degree accounting

### Lemma 2: completed-line multiplication

If $p$ has already been derived through degree $B_0$, then $qp$ can be
derived through degree

\[
                       \max(B_0,\deg q+\deg p).
\tag{5}
\]

For each monomial of $q$, multiply the completed line $p$ by its variables
one at a time, scale by its coefficient, and sum. Every intermediate
product has degree at most $\deg p+\deg q$. The earlier proof of $p$
is reused; it is not multiplied wholesale by $q$. The zero cases are
immediate. This is the reason the argument below does not accumulate a
cost proportional to the height of the source DAG.

### Lemma 3: Boolean-zero polynomials have same-degree certificates

If an ordinary polynomial $p$ of degree at most $d$ vanishes on every
Boolean assignment, it has a derivation from the Boolean axioms alone
through degree $d$.

To see this, reduce every positive power $x_i^a$ to $x_i$. For $a\ge2$,

\[
 x_i^a-x_i=(x_i^2-x_i)(1+x_i+\cdots+x_i^{a-2}).
\]

Telescoping this identity in each monomial gives

\[
                       p-\operatorname{ml}(p)
                            =\sum_i a_i(x)(x_i^2-x_i),
\tag{6}
\]

where every individual axiom multiple has degree at most $d$.
Here $\operatorname{ml}$ denotes squarefree reduction. The multilinear
polynomial $\operatorname{ml}(p)$ also vanishes everywhere, so it is zero:
write it as $p_0+x_n p_1$, evaluate at $x_n=0,1$, and induct on $n$.
Equation (6), expanded into monomial multiples, is an ordinary-PC
derivation with the stated bound. No free Boolean reduction is used.

The degree-zero and degree-one cases cause no exception: a multilinear
polynomial of those degrees that vanishes everywhere is already zero.
This lemma holds over any field on the Boolean cube; the particular
affine-flat applications below use $\mathbb F_2$.

## 3. Low-rank falsity indicators

For each nontautological affine clause $A$, choose a basis
$g_1,\ldots,g_{r(A)}$ from the span of its affine forms, and define

\[
                        q_A=\prod_{j=1}^{r(A)}(1-g_j).
\tag{7}
\]

As an ordinary polynomial, $\deg q_A\le r(A)$. On the Boolean cube it is
exactly the indicator of $Z(A)$: it is one precisely when all the affine
equations are zero. This uses that every value of an affine form over
$\mathbb F_2$ is zero or one.

For a proper raw CNF clause, take its literal forms themselves as the
basis. They are independent because they use distinct variables. Then
$q_A$ is exactly its raw clause polynomial in $\mathcal F$. In particular,
every raw initial line is low since $w\le R$.

If $A,B$ semantically imply $C$, then for every Boolean assignment

\[
                 q_C(1-q_A)(1-q_B)=0.
\tag{8}
\]

This says that an assignment falsifying the conclusion cannot satisfy
both premises. For a unary semantic inference $A\Rightarrow C$, the
corresponding identity is $q_C(1-q_A)=0$. These are identities of
functions; when they are used as polynomial equations below, Lemma 3
supplies the required ordinary-PC certificates.

## 4. The weighted replay lemma

Let $f\in P_{\le k}$ vanish on every high falsity flat in $\mathcal Z$.
We prove that the whole source refutation yields

\[
                             f\in C_{k+3R}(F).
\tag{9}
\]

The invariant is: for each **low** source line $A$, derive the ordinary
polynomial $fq_A$ through degree at most $k+3R$. Nothing needs to be
derived for a high line. Its contribution is the semantic fact that
$f$ vanishes on its falsity set. One fixed $f$ is used for the entire DAG.

For an initial line $A$, multiply the raw clause polynomial $q_A$ by $f$.
Lemma 2 bounds the cost by $k+w\le k+3R$.
A tautological line has $q_A=0$, and its weighted line is the PC zero
line. Consider any other low conclusion $C$.

### Both parents low

The induction hypotheses give $fq_A$ and $fq_B$. Derive

\[
       D=q_C(fq_A)+(1-q_A)q_C(fq_B).
\tag{10}
\]

The first product has degree at most $k+2R$, and the second at most
$k+3R$. By Lemma 2, their earlier derivation costs remain bounded by
$k+3R$. As ordinary polynomials,

\[
       fq_C-D=fq_C(1-q_A)(1-q_B).
\tag{11}
\]

The right side vanishes on every Boolean assignment by soundness (8),
and has degree at most $k+3R$. Lemma 3 derives this correction; adding it
to $D$ gives $fq_C$.

### One parent high

Suppose $A$ is high and $B$ is low. Derive $q_C(fq_B)$. The remaining
correction is

\[
                        fq_C(1-q_B).
\tag{12}
\]

Whenever $q_C=1$ and $q_B=0$, soundness forces $q_A=1$. The assignment
therefore lies in $Z(A)$, where $f=0$. Thus (12) is Boolean-zero.
Its ordinary degree is at most $k+2R$, because **the high-rank polynomial
$q_A$ never occurs in it**. Lemma 3 supplies the correction at this
degree. The case of the other high parent is symmetric.

### Both parents high

If $q_C=1$, at least one parent is false. The assignment lies in one of
the two high falsity flats, so $f=0$. Consequently $fq_C$ vanishes on
the whole Boolean cube. Lemma 3 derives it through degree at most $k+R$.

### Unary inference

For a low parent $A$, derive $q_C(fq_A)$ and add the Boolean-zero
correction $fq_C(1-q_A)$, costing at most $k+2R$. For a high parent,
$fq_C$ itself is Boolean-zero. This covers semantic weakening directly.

These arguments establish the invariant in topological order. The
final empty clause is low and has $q_C=1$, so its weighted polynomial is
$f$. This proves (9). The proof allows arbitrary earlier-parent reuse,
arbitrary parity support, and arbitrary rank on the high lines.

## 5. Restriction maps and rank-nullity

Let $Z$ be a nonempty affine flat of codimension $r$. There is an affine
coordinate bijection over $\mathbb F_2$ taking $Z$ to
$y_1=\cdots=y_r=0$. To construct it, take a basis of its defining
equations, choose one common zero, and extend their independent linear
parts to a basis of the dual space.

Substitute the inverse coordinate change into $f\in P_{\le k}$, set the
first $r$ coordinates to zero, and squarefree-reduce the remaining
polynomial. This defines a linear map

\[
       \rho_Z:P_{\le k}\longrightarrow
       \operatorname{ML}_{\le k}(y_{r+1},\ldots,y_n).
\tag{13}
\]

Affine substitution and squarefree reduction do not increase degree.
The codomain has dimension $b_k(n-r)$. By uniqueness of multilinear
representations,

\[
            \rho_Z(f)=0
               \quad\Longleftrightarrow\quad
            f\text{ vanishes at every point of }Z.
\tag{14}
\]

Form the joint restriction map

\[
             T:U\longrightarrow
                    \bigoplus_{Z\in\mathcal Z}
                         \operatorname{ML}_{\le k}(Z),
              \qquad T(f)=(\rho_Z(f))_{Z\in\mathcal Z}.
\]

Every member of $\ker T$ satisfies the hypothesis of the weighted
replay lemma, hence

\[
                          \ker T\subseteq U\cap C_{k+3R}(F).
\]

Rank-nullity gives

\[
 \dim U
   =\dim\ker T+\dim\operatorname{im}T
   \le \dim(U\cap C_{k+3R}(F))
           +\sum_{Z\in\mathcal Z}b_k(\dim Z).
\]

This proves (1), and (2) immediately yields (3) and (4).
If there are no high lines, the direct sum is zero and every
$f\in U$ is derived by the replay; the statement includes this case.

## 6. Generalizations that follow from the same proof

### Bounded-arity semantic rules

Suppose each inference has at most $a\ge1$ parents, with soundness
interpreted as their conjunction implying the conclusion. Replace
$B=k+3R$ by

\[
                              B=k+(a+1)R.
\tag{15}
\]

For a low conclusion $C$, list its low parents as $A_1,\ldots,A_t$,
where $t\le a$. Telescope

\[
 f q_C\left(1-\prod_{j=1}^{t}(1-q_{A_j})\right)
   =
   \sum_{j=1}^{t}
      q_C\prod_{i<j}(1-q_{A_i})\,(f q_{A_j}).
\tag{16}
\]

Every summand is derived from a completed weighted parent and has degree
at most $k+(t+1)R$. The missing correction is
$fq_C\prod_{j=1}^{t}(1-q_{A_j})$. If it could be nonzero at an assignment,
the conclusion would be false and every low parent true. Soundness then
forces some high parent false, on whose flat $f=0$. If no high parent
exists, soundness itself excludes the assignment. Lemma 3 completes
the replay. The dimension inequalities are unchanged, with the budget
in (15).

Thus a lower bound constructed with linear degree room and a large
separator can cover any fixed inference arity. There is no claim for an
unbounded-arity rule at the binary budget.

### Maximal separated-space formulation

Finite-dimensional linear algebra identifies the largest possible
separator dimension as

\[
 H_F(B,k)
   =\dim P_{\le k}
      -\dim\bigl(P_{\le k}\cap C_B(F)\bigr).
\tag{17}
\]

Choose a linear complement of the intersection inside $P_{\le k}$ to
attain it. Consequently the uniform lower bound can also be written
$S\ge H_F(B,k)/b_k(n-R-1)$. This is an exact reformulation; computing
$H_F$ or proving a useful lower bound for it is a separate task.
A refutation-degree lower bound alone supplies only that the direction
of the constant polynomial $1$ survives. The main quantitative
obligation is that many independent directions survive simultaneously.

## 7. What this does and does not establish

This is a theorem about proofs whose lines are affine clauses on the
original Boolean variables. It permits arbitrary DAG sharing, supports
of arbitrary size, semantic weakening, and arbitrary sound rules of a
fixed arity. Its proof uses ordinary PC over the one common field
$\mathbb F_2$.

It does not automatically apply to source proofs with extension variables,
mixed-characteristic arithmetic leaves, unrestricted integer reasoning,
arbitrary Boolean circuit lines, or all algorithms deciding SAT.
An application to those models would need a new simulation or a new
dimension argument with its costs included.

The proof above and a verified concrete separating-space construction
would establish a lower bound for the specified proof system. They
would not, by themselves, give a superpolynomial lower bound against
every polynomial-time SAT algorithm, or resolve P versus NP.

The external preprint's full imported Lean proof has not been built or
kernel-checked by this audit. This note is a separately inspectable
mathematical argument. The repository's finite experiments and selected
formal lemmas must retain their own narrower descriptions; neither is
a substitute for formalizing the entire theorem and its eventual
combinatorial application.
## Formalization follow-up

The [phase-21 ordinary-PC package](ordinary_pc_formalization.md) implements the
weighted semantic-DAG replay and its generic dimension transfer using actual
ordinary polynomials and primitive PC rules. The
[phase-22 restriction theorem](boolean_restriction_dimension.md) constructs
actual Boolean restrictions, proves their numerical binomial budgets, and
connects the source affine-clause DAG. Optimal parameterization existence,
intrinsic codimension, and the separator/counting chain were then separate
obligations. The [2026-11-08 completion](phase20_formalization.md) subsequently
closed these obligations for the F2 family and its explicit exponential bound.
Generalizations such as arbitrary parent arity retain their separate paper scope.

