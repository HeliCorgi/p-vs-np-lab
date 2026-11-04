# Keeping nonlinear correlations: a checked degree-five proof

[Implementation](../src/pnp_lab/polynomial_proof.py) · [tests](../tests/test_polynomial_proof.py) · [experiment](../experiments/correlation_polynomial.py) · [report](../results/correlation_polynomial.json).

The previous integer backend discarded all non-affine information on the
31-variable, 152-clause raw core. Here the same original clauses have a checked
polynomial-calculus refutation of degree five. Degree four is insufficient over
**every field**, by an elementary invariant proved below. The upper bound comes
from a newly discovered width-four resolution proof, translated into explicit
arithmetic instructions. The executable arithmetic checker is over F2; the
translation identity and the lower-bound argument apply over arbitrary fields.

This identifies exactly how much polynomial degree is needed on this fixed
example. It is not a new proof system, a complete bounded-degree searcher, or a
uniform bound for arbitrary SAT. [The proof-system boundary](correlation_proof_boundary.md)
records the relevant established general lower bounds.

## 1. Original clauses as Boolean equations

For a literal l, write its falsity factor as

\[
 f_l=x_v\quad(l=\neg x_v),\qquad f_l=1-x_v\quad(l=x_v).
\]

A clause C is satisfied exactly when its falsity polynomial

\[
                   f_C=\prod_{l\in C}f_l
\]

vanishes on a Boolean assignment. Work in
F[x_1,...,x_n]/(x_i^2-x_i), using the unique multilinear representatives.
Polynomial calculus permits linear combinations of known zero polynomials
and multiplication by a variable. Reaching the constant one refutes the
original clauses.

The executable certificate fixes F=F2, so addition is XOR and 1-x=1+x. Its
only operations are an original input clause, addition of two earlier
polynomials, and multiplication of an earlier polynomial by one original
variable. There is no instruction to assert a new polynomial, to invoke a SAT
oracle, or to trust an intermediate resolution clause.

The checker recomputes every polynomial from the original clause indices. It
expands input falsity factors independently of the translator, checks all
backward references, and requires the final polynomial to be exactly one.
The recorded `degree` is the exact maximum **charged** degree: multiplication
by x charges deg(p)+1 before Boolean reduction. Thus repeating a variable
does not hide a high-degree multiplication. The zero polynomial has degree
minus infinity, represented as -1 for this finite accounting convention.

This is at least as strict as allowing free multilinearization after every
step. The lower-bound proof below holds for that more permissive degree
measure too. The translated upper-bound proof only multiplies by variables
absent from the current clause indicator, so it needs no implicit Boolean
reduction and is also an ordinary polynomial-calculus derivation.

## 2. Translate resolution without losing the intermediate degree cost

Suppose resolution uses the pivot x on

\[
                 x\lor A,\qquad \neg x\lor B
\]

and produces the non-tautological resolvent E=A union B. A and B are sets of
nonpivot literals. A shared literal has the same sign, because E is not
tautological. Let A'=A minus B and B'=B minus A. Then, over any field,

\[
 f_{x\lor A}\,f_{B'}+f_{\neg x\lor B}\,f_{A'}
     =(1-x)f_E+x f_E=f_E.                                     \tag{1}
\]

Each parent is multiplied only by the false-literal factors missing from
its own nonpivot clause. Shared factors are not multiplied twice. Multiply
these factors one at a time. To multiply p by 1-x_i in ordinary PC, derive
x_i p and subtract it from p; in F2 this is an addition. Every factor adds
a variable absent from the current product. The largest intermediate
variable set is exactly the resolvent support together with the pivot.

Consequently a resolution proof of width w translates to a PC proof of
degree at most w+1. Counting only the output clause width would omit this
intermediate cost. This precise +1 convention is explicitly stated in
[Galesi, Kołodziejczyk and Thapen, *Polynomial Calculus Space and Resolution
Width* (2025), p.3](https://theoryofcomputing.org/articles/v021a006/v021a006.pdf).
The construction above supplies the needed simulation directly, independently
of any informal summary of the relation between width and degree.

On the raw core the resolution guide finds a 368-node proof, containing
115 input clauses and 253 resolutions. Its translation has:

| Measured proof quantity | Value |
| --- | ---: |
| Arithmetic nodes | 1,262 |
| Input / addition / variable multiplication nodes | 115 / 552 / 595 |
| Maximum charged degree | 5 |
| Sum of monomial occurrences across all stored nodes | 6,313 |
| Largest individual polynomial | 32 monomials |
| Counted symbolic visits | 15,003 |

The proof is a DAG and reuses previously established equations. These are
certificate measurements. Finding the guiding resolution proof has separate
row and pair counts, recorded in the report; they are not replaced by the
much smaller verification cost.

## 3. Why degree four is impossible on every proper linear 3-CNF

Here **linear** means that every clause has three distinct underlying
variables and any two distinct clauses have supports intersecting in at most
one variable. In particular, two different clauses cannot share the same
triple. It does not mean that the clause equations themselves are linear.
The signed 31-variable core and its all-positive same-support sibling both
have this property.

Let S_C be the triple supporting a clause C. Its polynomial f_C has degree
three, with leading monomial x^(S_C) and a nonzero coefficient. Define

\[
 V_4=\operatorname{span}_F\bigl(
     \{f_C:C\in F\}\ \cup\
     \{x_j f_C:C\in F,\ j\notin S_C\}\bigr).                  \tag{2}
\]

Three observations prove the invariant.

**Distinct highest monomials.** The quartic leading monomial of x_j f_C
is x^(S_C union {j}). No other indicated generator has the same quartic
leading monomial: two triples contained in a four-set would intersect in
at least two variables. Once the quartic coefficients are all zero, the
remaining cubic generators likewise have distinct leading triples. Hence
V4 contains no nonzero polynomial of degree at most two. In particular it
does not contain the constant one. This argument is valid over every field.

**Multiplication within a clause.** In the Boolean quotient, x_i f_C
is f_C when clause C contains the negative literal on i, and is zero when
C contains the positive literal on i. Consequently a quartic generator
x_j f_C is fixed or killed when multiplied by any variable in S_C union {j}.

**Closure under admissible multiplication.** Let p belong to V4 and suppose
the multilinear polynomial x_i p has degree at most four. Every quartic
monomial of p must contain i: otherwise multiplication creates a degree-five
monomial, and distinct quartic monomials not containing i create distinct
degree-five monomials, so they cannot cancel. By uniqueness of the quartic
leading monomials, every quartic generator with a nonzero coefficient in p
therefore contains i in its support. Those generators are fixed or killed
by x_i. The remaining cubic generators are taken to zero, themselves, or an
allowed quartic generator. Thus x_i p belongs to V4.

All axioms lie in V4, it is closed under linear combinations, and it is closed
under every variable multiplication that can occur in a degree-at-most-four
multilinear derivation. Induction on the proof therefore keeps every line
inside V4. Since 1 is outside V4, there is no such refutation.

The argument also rules out ordinary PC refutations of degree at most four:
map each ordinary proof line into the Boolean quotient. Boolean axioms become
zero, reduction never increases degree, and each inference is one of the
operations covered above. Combined with the independently checked resolution
guide and (1), this proves that the raw core's minimum PC refutation degree
is exactly **five over every field**. This finite threshold is not claimed
as an asymptotic lower bound or an unpublished proof-complexity principle.

## 4. Static lifting and dynamic derivations are different experiments

The existing [static affine-cover backend](overlap_refutation.md) can read each
raw clause's forbidden assignment as an affine event of rank three. There is
no need to duplicate that backend. The report exhausts its complete degree
three and four multiplier spaces on both signings, without a row cap.

On the UNSAT core, degree three uses 152 rows with rank 152. Degree four
generates 4,864 rows and has rank 4,408, equal to 152*(1+28): multipliers on
the clause's own three variables are either zero or the original clause;
the 28 outside-variable multiples have distinct quartic leading monomials.
The constant one is absent in both runs. The positive signing has the same
ranks, as the characteristic-independent argument predicts.

These exhausted **static** searches are separate from the invariant for
the full dynamic calculus. The new upper-bound certificate feeds derived
equations into later multiplications. No claim is made that the full static
degree-five space has been exhausted or that it lacks a refutation. In
particular, a memory or row cap would establish neither fact.

## 5. API, resources, and what the result does not establish

`resolution_to_polynomial(n, clauses, resolution_certificate, ...)` translates
a checked guide. `polynomial_refute(...)` first asks the bounded-width resolution
finder for that guide. `check_polynomial_proof(...)` needs only the original CNF
and the arithmetic certificate. **Discovery is resolution-guided; it is not a
complete decision procedure for bounded-degree PC.** An unsuccessful guide
or capped translation returns UNKNOWN with no certificate.

Proof budgets limit the number of arithmetic nodes, the total monomial
occurrences stored across those nodes, and a documented count of symbolic
visits. Source resolution replay also checks its node count before reading
the nodes, bounds the cumulative stored literal count by `max_work`, and
applies `max_degree` to actual source-clause widths when that cap is set.
This prevents a tiny arithmetic budget from hiding unbounded source replay;
a loose declared source width does not consume this budget. A degree cap
limits the charged degree. Resolution discovery retains
its own row and pair caps. Monomials use original variable-label tuples rather
than a bit position equal to a potentially huge variable name. Polynomial
expansion is bounded by the proof's degree and visits; the algorithm never
allocates every possible degree-five monomial just to verify a supplied proof.
These counters are distinct from wall time, process memory, and the number of
monomials that an optimally scheduled proof could keep simultaneously alive.

If degree or width is allowed to grow with the input, the number of possible
monomials or clauses grows accordingly. Existing lower bounds on these known
proof systems remain applicable to their stated families. The successful
31-variable example demonstrates a concrete correlation missed by affine
projection and now represented in a small checked proof. It does not supply
a fixed polynomial bound on discovery or certificate size for all SAT inputs,
nor a lower bound against arbitrary algorithms or extension variables.
