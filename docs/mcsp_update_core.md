# Direct attempts at the MCSP update lower bound

The target is the all-algorithm, all-polynomial lower bound stated in
[the streaming note](mcsp_streaming_gate.md). Its implication to P≠NP is
known; **the target itself remains unproved**. This continuation tests
three proposed ways to supply its missing argument. The results reject
particular inferences and give an elementary repair bound, not a new
general complexity lower bound.

The basis is binary AND/OR and unary NOT, with each gate counted; constants
and input wires are free. Complemented inputs are not supplied for free.
Input words are in lexicographic order, the first variable most significant.

The subsequent [state-reduction attempt](mcsp_state_reduction.md) also
failed to obtain a valid all-algorithm lower bound. The current MCSP
proof attempts are parked; these notes retain their exact limited scope.

## 1. Hard prescribed-witness validation does not force hard repair

Let the state be the zero circuit C=0, the already read prefix consist
entirely of zeros, and the next bit also be zero. Finding **some** valid
repair is immediate: keep C=0. Nevertheless, checking a **specified**
candidate D is coNP-complete even on this family of reachable prefixes.

Take an arbitrary circuit G on m variables with g gates. Choose n with
n >= m+1 and n^2 >= g+2; a polynomially bounded n suffices. Introduce a
most significant control bit t, the m inputs y of G, and unused padding
variables z. Set

\[
 D(t,y,z)=\neg t\wedge G(y),\qquad i=2^{n-1},\qquad b=0,\qquad s=n^2.
\]

D has g+2 gates and meets the budget. The interval x<i consists exactly
of the inputs with t=0, and every assignment to y occurs there. At x=i,
t=1 and D(i)=0 automatically. Thus

\[
 [D(i)=0\ \land\ \forall x<i:D(x)=C(x)]
 \quad\Longleftrightarrow\quad\forall y:G(y)=0.
\]

The compact tuple and padded descriptions are constructible in polynomial
time in G's encoding. This reduces circuit UNSAT to prescribed-candidate
validation. Nonvalidity has a short witness x<i where the circuits differ,
or the failed condition at i; syntax and size are directly checkable.
Validation is therefore in coNP as well. This is an ordinary circuit-UNSAT
reduction, not a new separation.

On **every** instance in this reduction, unrestricted Repair has the easy
answer C=0. A search procedure can return it without inspecting D. Thus
hardness of the prescribed-candidate predicate, including a query whose
output-description prefix fixes all of D, does not establish hardness
of finding an arbitrary valid repair. Nor does it show that every
streaming algorithm must perform that validation.

### A compact input and a stream have different time budgets

If D is known before the stream, check it against the truth table with
one circuit evaluation per arriving bit. Store D, an n-bit index, the
evaluation workspace, and a mismatch flag. Work per bit is polynomial
in s+n, space is O(s log(s+n)+n), and final reporting is constant time.
On a zero stream this checks whether D is identically zero in N=2^n
updates. That is consistent with coNP-completeness on the exponentially
shorter **compact** input.

A hard-looking compact computation can therefore be spread over the
long stream. For a candidate chosen only at the end, an argument must
explain why useful information could not be prepared earlier. The
brute-force cost of a fresh validation does not prove this for all
streaming representations.

## 2. Minimum circuit size is not a strict update counter

For a truth-table prefix p define

\[
 \mu(p)=\min\{|C|:C\text{ agrees with }p\}.
\]

Extensions are unrestricted outside p. This is finite and nondecreasing
under extension. Charging every forced change of a minimum-size
representative to a strict increase in mu fails as follows.

For n=3 and the five-bit prefix p=00101, take

\[
 F_0=(x\lor y)\wedge\neg z,\qquad F_1=x\lor(y\wedge\neg z).
\]

Both have three gates:

| Input xyz | F_0 | F_1 |
|---|---:|---:|
| 000 | 0 | 0 |
| 001 | 0 | 0 |
| 010 | 1 | 1 |
| 011 | 0 | 0 |
| 100 | 1 | 1 |
| 101 | 0 | 1 |
| 110 | 1 | 1 |
| 111 | 0 | 1 |

**Minimality without enumeration.** The prefix forces dependence on all
three variables: compare 000 with 100 for x, 000 with 010 for y, and
010 with 011 for z. A circuit with at most two gates depending on three
variables must use two binary gates. It has no NOT gate and is monotone.
But 010 <= 011 coordinatewise, while the values are 1 and 0. This is
impossible. No circuit of size at most two agrees with p.

The two displayed witnesses match p and give opposite values at the next
position 101. Hence

\[
                 \mu(p)=\mu(p0)=\mu(p1)=3.
\]

Whatever a chosen minimum-size representative predicts next, the
opposite bit forces a different function while the minimum size stays
three. The proposed strict charge fails even for genuinely minimum-size
representatives. Counting unused syntactic gates does not repair it.

This forces one change, not a costly change: the replacements are tiny
and explicit. It gives no superpolynomial update count. It does not
refute every potential function or a further hypothesis restricted to
prefixes near the n^2 threshold.

## 3. A universal one-point repair bound

For an n-input circuit C of size r, input a, and required bit b, there
is a circuit D of size at most r+2n+3 agreeing with C everywhere except
possibly a and satisfying D(a)=b. Constructing D is polynomial time
in the encoded C,a,b.

If C(a)=b use C. Otherwise build the point indicator

\[
 \delta_a(x)=\bigwedge_{j=1}^n
       \begin{cases}x_j&a_j=1,\\ \neg x_j&a_j=0.\end{cases}
\]

This costs at most n NOT gates and n-1 AND gates. Set D=C XOR delta_a,
implementing the XOR in the counted basis by

\[
              D=(C\lor\delta_a)\wedge\neg(C\wedge\delta_a).
\]

There are four further gates, sharing C and delta_a, for total overhead
at most 2n+3. Exactly one input value is flipped. In particular, the
entire earlier prefix is preserved.

Applying this to a minimum representative proves, for every prefix
shorter than 2^n and either next bit b,

\[
       \mu(p)\le\mu(pb)\le\mu(p)+2n+3. \tag{1}
\]

If mu(p) <= s-(2n+3), **both** next bits have extensions within budget s.
When a representative of that size is actually available, the repair
is efficient. Existence alone does not give an efficient way to find it.

If pb is the first prefix without a size-s extension, (1) gives

\[
                    s-(2n+3)<\mu(p)\le s. \tag{2}
\]

An adversary forcing unavoidable rejection by the next bit must first
reach this narrow **semantic** interval. Filling a stored circuit with
gates establishes nothing about mu(p). Equation (2) does not locate the
first rejection, prove that recognizing it is hard, or describe every
possible source of expensive computation on YES inputs.

## What remains unresolved

The inference from prescribed-candidate hardness fails even on reachable
states. Strict potential growth fails on two explicit three-gate
functions. One-bit adversaries with a known sufficiently short
representative admit an efficient repair. These branches stop at those
specific failures.

The required argument must still apply to **every** uniform streaming
algorithm, including those that compute during earlier input, store a
different representation, and never compute mu or solve Repair. It must
exclude every fixed polynomial bound on space and update/reporting time.
Nothing above supplies that argument. The missing core is not a small
final technical lemma: proving it would already imply P≠NP.

**Status: no new general lower bound, no complete P-versus-NP proof, and
no proved surviving route through the missing core.** These elementary
statements are paper proofs, not Lean formalizations.

## Finite checks actually run

[`experiments/mcsp_update_gate.py`](../experiments/mcsp_update_gate.py)
is a bounded audit, not an MCSP solver. Its
[deterministic report](../results/mcsp_update_gate.json) checks:

- All semantic DAG states through two gates on three inputs: 9 states
  at one gate and 66 at two, yielding 40 functions including zero-gate
  functions. None matches 00101. The three-gate witnesses are evaluated
  separately. Merging states with equal sets of available functions is
  exact: future gates have the same possible operands; duplicate-value
  gates can be removed and their later uses rewired.
- Every source function on 1, 2 and 3 inputs and every point to flip:
  2,120 patched circuits and 16,656 truth-value comparisons. Counted
  AND/OR/NOT gates are directly evaluated, with the original truth table
  and one flipped bit as the independent expected result. Maximum added
  gate counts are 5, 7 and 9, matching 2n+3.
- All 16 two-input source functions for the prescribed-candidate
  reduction. Only the zero source makes the prescribed candidate valid;
  the zero circuit is a valid unrestricted repair in all 16 cases.
  Padding and the n^2 gate budget are checked explicitly.

The all-n construction and coNP reduction follow from the arguments
above, not extrapolation from these finite checks. The report is included
in the existing reproduction command:

```sh
python3 experiments/mcsp_update_gate.py --out-dir reproduced
python3 scripts/reproduce.py --out-dir reproduced --check
```
