# New strategy: exact Boolean evaluation by small matrices

2026-11-06 JST. This is a new P=NP-side attempt, independent of the parked
MCSP lower-bound program. The proposal is to make Boolean reasoning
compatible with ordinary finite-dimensional linear algebra, then decide
SAT by a matrix zero test. **No complete P-versus-NP proof was obtained.**
The universal matrix construction is ruled out below; an efficient
formula-dependent complete construction has not been found.

The argument uses standard orthogonal-idempotent decomposition. It is
written out to assess the proposed algorithm, not presented as a new
representation theorem or a general lower bound on SAT algorithms.

## 1. The proposed algorithm and its missing guarantee

Let n,d>=1. Choose n matrices X_1,...,X_n in M_d(K), where K is a field, with

\[
                  X_i^2=X_i,\qquad X_iX_j=X_jX_i.
\]

Evaluate Boolean formulas using

\[
 0\mapsto0,\quad1\mapsto I,\quad
 \neg A\mapsto I-A,\quad
 A\wedge B\mapsto AB,\quad
 A\vee B\mapsto A+B-AB.
\]

For the executable audit K=F2, XOR maps to matrix addition. All intermediate
values commute and are idempotent, by induction on the Boolean operations.
In particular, the contradictory Boolean expression x AND NOT x evaluates
to X(I-X)=0. This addresses the Boolean semantics that ordinary polynomial
identity testing failed to preserve in the earlier attempt.

With explicit matrices over F2, checking idempotence and commutation
costs O(n^2 d^3) bit operations using elementary matrix multiplication.
Evaluating an m-gate formula or circuit costs O(m d^3). All stored field
elements have one bit. The elementary zero test is cheap when d is
polynomial in the input length.

The missing condition is **completeness**:

\[
             F\text{ satisfiable}\quad\Longrightarrow\quad F(X)\ne0.
\]

Soundness of a nonzero result follows from the decomposition below.
Zero is otherwise **UNKNOWN**, not an UNSAT certificate. Merely checking
the algebraic laws on the X_i does not establish completeness.
Variable-free constant formulas can be handled directly.

For a fixed F2 tuple using multiplication for AND and addition for XOR,
these laws are also forced by soundness on all formulas: the identically
false formulas `x XOR (x AND x)` and `(x AND y) XOR (y AND x)` require
respectively X+X^2=0 and XY+YX=0. Thus simply dropping the validity checks
does not make this particular gate-evaluation scheme a sound SAT test.

## 2. Classification: a d-dimensional representation sees at most d words

For a Boolean word a in {0,1}^n, define

\[
 E_a=\prod_{i=1}^n
       \begin{cases}X_i&a_i=1,\\ I-X_i&a_i=0.\end{cases}
\]

These products are well-defined independently of order. Idempotence and
commutation imply

\[
 E_a^2=E_a,\qquad E_aE_b=0\ (a\ne b),\qquad
 \sum_aE_a=\prod_i(X_i+(I-X_i))=I.
\]

Thus K^d is the direct sum of the spaces im(E_a). Indeed, the sum is all
of K^d by the last identity, and applying E_b to a linear relation among
the summands isolates its b component. In particular,

\[
          \sum_a\operatorname{rank}E_a=d,\qquad
          |R_X|\le d,\quad R_X:=\{a:E_a\ne0\}. \tag{1}
\]

On im(E_a), each X_i acts as a_i times the identity. Induction on the
formula gives

\[
       F(X)=\sum_a F(a)E_a,\qquad
       F(X)\ne0\ \Longleftrightarrow\
       \exists a\in R_X:F(a)=1. \tag{2}
\]

For the reverse zero-test implication, multiply the displayed sum by
E_a; different summands cannot cancel, even in characteristic two.
This proves that the representation tests satisfaction on the set R_X,
with possible multiplicities in its eigenspaces. A non-diagonal basis
does not add represented assignments. No assumption about sparse entries
or rank-one variable matrices is used.

## 3. Uniform completeness forces exponential dimension

Suppose one tuple X_1,...,X_n is chosen independently of F and must detect
every satisfiable formula on those n variables. For each word a, take the
CNF of n unit clauses fixing the variables to a. Its only satisfying
assignment is a, and its matrix value is E_a. Completeness requires E_a
to be nonzero for **every** a. Equation (1) gives

\[
                              d\ge2^n. \tag{3}
\]

These singleton formulas have polynomial encoded length. The argument
already concerns detecting one witness, not counting all models or
requiring an explicit representation of all solutions as output.
The bound is attained by dimension 2^n diagonal matrices with diagonal
entries (X_i)_{a,a}=a_i. That construction enumerates all assignments.

Even a restriction to proper three-literal clauses would not remove
the obstruction for n>=3. A unit literal l can be replaced by the four
clauses (l OR epsilon*y OR eta*z), for all signs epsilon and eta and
two other distinct variables y,z. Their conjunction is exactly l.
Applying this replacement to all n units preserves the singleton with
only 4n proper three-clauses and no additional variables.

Randomization independent of F also does not solve this problem. If the
dimension is at most d, then the average, over all a, of the probability
that E_a is nonzero is E[|R_X|]/2^n <= d/2^n. Some singleton formula
therefore has detection probability at most d/2^n. For k such samples,
the union represents at most kd words. This statement does not concern
matrix choices that inspect the formula.

## 4. Witness extraction is constructive and polynomial

The represented assignments are not merely an abstract obstruction.
They can be recovered in polynomial time from the explicit matrices.

First suppose Y=F(X) is nonzero. Choose a nonzero column v of Y. Since
Y^2=Y, we have Yv=v. For i=1,...,n:

1. Compute w=X_i v.
2. If w is nonzero, set a_i=1 and replace v by w.
3. Otherwise set a_i=0 and leave v unchanged.

The vector remains nonzero, Yv=v remains true, and every previously
fixed eigenvalue remains true because the matrices commute. Idempotence
ensures X_i w=w in the nonzero branch. At the end X_i v=a_i v for all i.
Hence Yv=F(a)v=v and F(a)=1. The extraction takes O(nd^2) field operations
after Y is available. It uses neither a search over 2^n words nor a
general-purpose eigensolver.

To recover **all** of R_X, start with P=I. If P is nonzero, use the same
procedure with Y=P to obtain a word a. Compute its E_a using n matrix
multiplications, record a, and replace P by P-E_a. The invariant is
that P is the sum of the not-yet-recorded atoms. Thus PE_a=E_a, and each
iteration removes a nonzero direct summand. After at most d iterations,
P=0. This recovers exactly R_X in O(nd^4) elementary field operations.
For F2 these are polynomial bit costs on the explicit matrices.

Consequently this whole algebraic representation can be converted to
an explicit list of at most d assignments in polynomial time. Its
zero test is exactly testing F on that list. The dimension bound alone
is not being used to hide an intractable diagonalization problem.

## 5. Formula-dependent matrices: the construction is the full problem

Allowing the tuple to depend on F evades (3). If F is satisfiable, any
one satisfying assignment a gives a dimension-one representation X_i=a_i
with F(X)=1. Such small representations therefore **exist** for every
satisfiable input. This is no efficient construction yet.

For a fixed field F2, the following algorithmic statement is equivalent
to P=NP:

> A single deterministic polynomial-time procedure, given any Boolean
> formula F, outputs explicit commuting idempotent matrices of dimension
> polynomial in |F|, such that F satisfiable implies F(X) is nonzero.

If the procedure exists, evaluate F(X) and use (2) for soundness and the
stated completeness for the other direction. This decides SAT in
polynomial time. Section 4 also yields an ordinary satisfying assignment.

Conversely, if P=NP, decide F and recover a satisfying assignment by
the standard polynomial number of variable-fixing SAT calls. Output
the resulting one-dimensional matrices on SAT inputs, and all-zero
scalar matrices on UNSAT inputs. All matrices obey the required laws;
every valid representation evaluates an unsatisfiable F to zero.

Thus a formula-dependent complete selector cannot be installed as an
unproved helper lemma. It is a possible restatement of the algorithmic
goal, not a solution. No independent construction of that selector was
obtained in this investigation.

## 6. Invalid shortcuts and scope of the stopping decision

Over F2 the matrices

\[
 P=\begin{pmatrix}1&1\\0&0\end{pmatrix},\qquad
 Q=\begin{pmatrix}1&0\\1&0\end{pmatrix}
\]

are individually idempotent, but PQ=0 while QP is nonzero. Dropping
commutation breaks the identity x AND y = y AND x. Dropping idempotence
also breaks x AND x = x, for example with the nonzero square-zero matrix
whose only nonzero entry is in its upper-right corner.

These examples do not exclude every noncommutative or matrix-based SAT
method. The theorem concerns precisely the stated homomorphic Boolean
evaluation. Likewise, an exponential-dimensional matrix may have a short
implicit description; that alone supplies no efficient multiplication
or zero-test algorithm for the resulting implicit objects.

The fixed universal polynomial-dimension construction is therefore
**rejected before developing a general SAT solver**. The formula-dependent
version remains the original witness-discovery problem in a different
representation. A proof mechanism for constructing it has not been found.
The MCSP branch stays parked, and there is still no active complete-proof
candidate. These are paper arguments, not additional Lean theorems.

## 7. Executed finite audit

[`experiments/boolean_matrix_sat.py`](../experiments/boolean_matrix_sat.py)
implements finite F2 matrix operations, validity checks, direct circuit
evaluation, and the polynomial witness/support extractors. It uses full
atom enumeration only as an independent bounded reference in the audit.
The [report](../results/boolean_matrix_sat.json) records:

| Check | Executed scope/result |
|---|---|
| All 2-by-2 idempotents | 8 out of the 16 binary matrices |
| All valid triples on three variables | 176 commuting triples; 8 represent one assignment and 168 represent two |
| Every three-variable Boolean function on each tuple | 45,056 checks; 33,280 extracted satisfying witnesses verified against truth tables |
| SAT inputs missed by zero evaluation | 11,600 tuple/function pairs; none is reported as UNSAT |
| Original circuit semantics | 64 seeded ten-gate circuits evaluated on each tuple: 11,264 cases, compared against independent Boolean truth tables |
| Polynomial support extraction | 177 cases compared with exhaustive atom support, including the dimension-eight control |
| Full dimension-eight representation | All 256 three-variable functions detected correctly |
| Invalid laws | Noncommuting and nonidempotent controls rejected |

The fixed two-dimensional counterexample with all X_i=0 sees only word
000 and misses, for example, the singleton word 001. Non-diagonal tuples
are included in the exhaustive audit. The all-n claims follow from the
proofs above, not extrapolation from these finite counts.

```sh
python3 experiments/boolean_matrix_sat.py --out-dir reproduced
python3 scripts/reproduce.py --out-dir reproduced --check
```
