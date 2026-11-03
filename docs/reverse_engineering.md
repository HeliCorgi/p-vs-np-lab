# Working backward from the solution criterion: XOR plus nonlinear constraints

This note connects [the exact P versus NP criterion](solution_criteria.md) to
the implemented [mixed solver](mixed_solver.md). It separates three results:
an explicit reduction covers an NP-complete mixed constraint language; the
current quotient enumerator has an exact all-input correctness argument and
an observation-rank upper bound; and a specific family forces this enumerator
to take superpolynomial time. None is a resolution of P versus NP, and no
novelty claim is made for these elementary constructions.

**Stage 3 follow-up:** [certified parity cuts](parity_cuts.md) now add sound
CNF-implied XOR equations before this baseline search. They remove the
exactly-one/even obstruction below but leave explicit exact-two and
bridge-encoded odd-cycle obstructions. A stronger Lean-checked theorem shows
that the bridge CNF alone entails no nontrivial affine equation at all.
Consequently the next unresolved step requires reasoning jointly with the
existing XOR constraints, conditional consequences, or a different treatment
of the nonlinear residual; merely making CNF-only affine extraction more
complete cannot solve this bridge family. The baseline analysis below remains
an analysis of `solve_mixed`, not the new preprocessing wrapper.

## 1. Coverage already reaches 2-CNF plus three-variable XOR

The implementation's decision problem is

\[
H(A,b,F)\ :=\ \exists x\in\{0,1\}^n:
      Ax=b\pmod2\ \land\ F(x),
\]

where `A` is an explicitly represented binary matrix, `b` is a binary vector,
and `F` is an explicitly represented CNF. Its API receives an
`AffineRelation` with an explicit scope and a CNF using indices into that
scope. The complexity analysis includes construction and normalization of the
input affine object.

Use `N` for the full input bit length. Parsing specifies variable names,
repeated variables in XOR rows, empty rows, empty clauses, and constants. The
explicit variable list ensures `n ≤ O(N)`. A sparsely encoded enormous unused
variable index is not a license to allocate that many columns.

A stronger coverage example than simply allowing arbitrary CNF is the
following clause gadget. For three literal truth values `a,b,c`,

\[
 a\lor b\lor c
 \quad\Longleftrightarrow\quad
 \exists u,v,w:\quad
 (a\lor u)\land(b\lor v)\land(c\lor w)
 \land(u\oplus v\oplus w=0).
\]

If all three literals are false, the binary clauses force `u=v=w=1`, which
violates even parity. If any literal is true, set its corresponding helper
to zero and the other two helpers to one. Every binary clause and the XOR
then holds. Literal negations or repeated original literals do not change
this argument: each of the three positions has its own fresh helper.

Give each of the `m` original 3SAT clauses its own three fresh helpers. This
produces `3m` binary CNF clauses and `m` XOR equations of width three, with
`n+3m` variables, in polynomial encoded size and construction time. For each
fixed original assignment, extension exists exactly when every original
clause is satisfied. Projecting any mixed model recovers a 3SAT model.
Short nonempty source clauses can be padded by repeating a literal; an empty
source clause needs an explicit UNSAT case. Exact-three-literal 3SAT already
suffices for NP-hardness.

An assignment checks all output constraints in polynomial time, so this
mixed language is in NP. Together with 3SAT completeness [C], the gadget
proves that **2-CNF plus three-variable XOR is NP-complete**. Separately,
2-CNF has a polynomial-time implication-graph algorithm [APT], and XOR systems
have Gaussian elimination. Their individual tractability does not imply
tractability of their conjunction. The construction and implementation are
recorded in [the reduction note](two_cnf_xor_reduction.md).

The reduction preserves decision and projection to original assignments,
**not model counts**. If `s` of a clause's three literal positions are true
after any padding,
there are zero helper extensions when `s=0` and `2^(s-1)` when `s≥1`: the
false positions are fixed to one, and the remaining `s` helper bits satisfy
one independent parity equation. Freshness makes the extension counts
multiply across clauses. This is not a parsimonious reduction.

The simpler coverage route remains valid: arbitrary 3CNF maps to an empty
XOR part and that same CNF. If nonempty XOR is required, add a fresh variable
with the equation `z=0`. The binary-clause gadget shows that arbitrary CNF
width is not needed for general NP-complete coverage.

For an exact-three-literal source with `m` clauses and all `n` original
variables actually occurring, the `m` XOR rows have disjoint helper scopes and rank `m`. All original and
helper variables occur in non-tautological binary clauses. Under the current
solver's normalization, this gives `d=r=n+2m`, using the definitions below.
Unused declared original variables add to `d` but not to `r`. Thus this
reduction establishes coverage; it does not accelerate the current
enumerator. On an UNSAT reduced instance, that enumerator still visits all
`2^r` cells.

A promise such as small nonlinear width, bounded treewidth, or low observation
rank changes the class being solved. Either prove that the reduction's image
always satisfies the promise, or state the result as a restricted algorithm.
In particular, a small width for each constraint does not bound `r`.

## 2. Distinguish free dimension d from observation rank r

Let `ρ = rank(A)`. If the linear equations are inconsistent, the mixed system
is UNSAT. Otherwise write the affine solution set as

\[
 x=x_0+Bt,\qquad t\in\mathbb F_2^d,\qquad d=n-\rho.
\]

The columns of `B` form a nullspace basis, so this is an injective and onto
parameterization. Equivalently, each variable has the form

\[
 x_i=c_i\oplus\langle a_i,t\rangle.
\]

A reference algorithm that evaluates `F(x0+Bt)` on all `t` would use
`2^d poly(N)` time. **The implemented algorithm does not generally enumerate
all those points.** It removes tautological clauses, repeated literals, and
duplicate clauses, and lets `S` be the set of indices still occurring. It
then defines

\[
 r=\dim\operatorname{span}\{a_i:i\in S\},\qquad 0\le r\le d.
\]

This is the observed coefficient rank. It is not the rank of `A`, the number
of free variables, or a minimum measure of semantic nonlinearity. Unit
clauses are included in `S`; the normalization does not perform unit
propagation or general affine-aware simplification.

Choose a basis `b_1,...,b_r` for the observed span and define

\[
 q(t)=(\langle b_1,t\rangle,\ldots,\langle b_r,t\rangle).
\]

The original CNF is constant on every fiber of `q`: all variables in its
non-tautological clauses have identical values at two points with the same
`q`, and the removed tautological clauses are always true. The observation
basis is independent, so `q` is onto. The implementation computes a right
inverse `L` from RREF pivot columns and checks the representative `t=Lz` for
each `z ∈ F_2^r`. Every possible CNF truth value within the affine solution
set is represented. A satisfying representative lifts to a valid witness;
rejecting every representative proves UNSAT. Each fiber has `2^(d-r)` points,
which also explains the exact count in exhaustive mode.

Parameterization, observation-basis construction, and each cell evaluation
use polynomial bit work on explicit finite inputs. The resulting upper bound
for this construction is

\[
 T(N)=O\!\left(\operatorname{poly}(N)+2^r\operatorname{poly}(N)\right).
\]

If a fixed promise guarantees `r ≤ c log(N+1)`, this is polynomial on that
promise. A large `d` can coexist with small `r`; unobserved directions need
not be enumerated. A polynomial total does not follow when `r` grows
unrestrictedly. Both observation and free ranks need to be reported.

For the complete decision procedure use `max_cells=None` and
`exhaustive=False`; SAT may stop at the first witness, while UNSAT requires
full coverage. A budget can return UNKNOWN and is not a total SAT/UNSAT
decider. Disabling both trace and certificate storage keeps the working space
polynomial, without changing the required UNSAT cell count. A requested full
certificate contains the rejecting cells and can have exponential size; its
checker is polynomial in input plus certificate size, not necessarily in `N`.

The all-input mathematical argument is in [mixed_solver.md](mixed_solver.md).
[Formal/QuotientSearch.lean](../Formal/QuotientSearch.lean) proves the abstract
quotient/lift and finite-scan logic under its hypotheses. To apply that
formal theorem to this program, one still needs the bridge from the original
CNF to a predicate of `q`, valid affine lifts, the right-inverse property,
complete enumeration, and the correctness of the Boolean evaluator. The
Python implementations of normalization, Gaussian elimination, lifting,
parsing, and certificate checking have not been formally verified end to end.
The separate theorem `bitVectors_length` does not formalize the Python cost.

## 3. The present algorithm already has a superpolynomial worst case

For every integer `k≥3`, use `k` Boolean variables and impose

\[
 x_1\oplus\cdots\oplus x_k=0
\]

alongside the exactly-one CNF

\[
 F_k=(x_1\lor\cdots\lor x_k)
     \land\bigwedge_{1\le i<j\le k}(\neg x_i\lor\neg x_j).
\]

The CNF requires exactly one true variable, hence odd parity; the XOR requires
even parity. The mixed system is therefore UNSAT, although each part alone
is satisfiable. There are no empty or unit clauses and the XOR system itself
is consistent.

The one nonzero XOR row has rank one, so `d=k-1`. All variables occur in the
CNF after the implementation's normalization. In particular, the `k-1` free
variables' coordinate-unit forms are observed, so `r=d=k-1`. The only early
exit inside the unbudgeted decision scan is a satisfying witness, which
cannot exist. Consequently this exact implementation visits **exactly
`2^(k-1)` quotient cells even with `exhaustive=False`**, regardless of whether
trace or certificate output is requested.

There are `1 + k(k-1)/2` CNF clauses and `k^2` literal occurrences. With ordinary
binary variable indices and explicit variable names, an encoding has
`N=O(k^2 log k)` bits. Since `2^(k-1)` eventually exceeds every fixed polynomial
in that encoding length, the loop count gives a **superpolynomial worst-case
lower bound for the current algorithm**. It is exponential in `k`; we do not
claim a `2^Ω(N)` lower bound in the full encoded input length.

This is an all-`k` argument from the family and the loop's control flow, not
an extrapolation of timings or finite measurements. The experiment generator
in [mixed_constraints.py](../experiments/mixed_constraints.py) restricts its
own enumerated examples to small `k`; the solver has no such scope limit, and
the mathematical family is defined above for all `k≥3`. The width-`k`
at-least-one clause means this particular family belongs to the general
XOR+CNF class; the 2-CNF plus three-variable-XOR reduction in Section 1 is a
separate coverage argument.

Accordingly, the gap is stronger than “a polynomial bound has not yet been
proved.” The current all-cell enumeration cannot have such a bound on every
input. The syntactic rank bound `r=O(log N)` is false on this family. A future
method must change the computation, exploit nonlinear reasoning without
checking every observable cell, or prove a different global bound for a
specified restricted input class.

The contradiction in this family is elementary and another algorithm can
recognize it quickly. On the affine space its residual CNF is identically
false, even though this implementation computes a large observation rank.
Thus the result does not lower-bound every SAT algorithm or prove `P≠NP`.
Discovering a more compact semantic summary is itself a computation whose
correctness and total cost must be accounted for.

The existing [parity example](parity_projection.md) makes a related point:
ordinary auxiliary-free CNF can expand exponentially, while native XOR stays
compact. Changing representation avoids that particular obstruction, but it
does not establish a polynomial total for arbitrary mixed systems.

There is also a precise encoding distinction: the binary OR relation has
three satisfying assignments, whereas a nonempty affine relation has
power-of-two cardinality and remains affine under projection. Affine
auxiliaries alone therefore cannot give a relation-preserving encoding of OR
on its original variables. This does not exclude every polynomial-time
satisfiability-preserving reduction from SAT to linear equations; such a
reduction would itself imply `P=NP`. The two claims have different quantifiers.

## 4. Proof obligations for each transformation

For a transformation of a state `S` to `S'`, record the following contract.

| Item | Required content |
|---|---|
| Scope | Original variables, retained boundary variables, hidden variables, and pinned constants are explicit. |
| Preconditions | The rule's assumptions are stated and checked, or proved as invariants. |
| Semantics | For every retained assignment `a`, `a` extends to a solution of `S` if and only if it extends to a solution of `S'`. |
| Witness map | If new auxiliary coordinates are used, show how to recover an original satisfying assignment. |
| Refutation | Every UNSAT conclusion follows from an exact inconsistency condition or complete case analysis. |
| Construction | Give the algorithm for finding the rule application, not just the transformed object. |
| Size and cost | Bound output size, working bit lengths, and bit operations using explicit input parameters. |
| Progress | Identify a well-founded measure for termination; separately bound the total number of states visited. |

The semantic contract may be weakened to equisatisfiability when a step only
needs a decision answer, but that weakening must be deliberate. It cannot be
used silently by later code that assumes the full boundary relation or
witness reconstruction.

Some concrete obligations follow immediately:

- Row swaps and addition of one XOR equation to another preserve the linear
  solution set. Pivot elimination must account for right-hand sides and
  distinguish a redundant `0 = 0` row from contradictory `0 = 1`.
- Substituting affine expressions into nonlinear constraints must preserve
  their exact Boolean meaning. Expressions or shared circuits can be kept
  explicitly; expanding them into ordinary CNF is a separate construction
  with its own size bound.
- Splitting on an actual Boolean variable is complete because every solution
  has exactly one of its two values. A more elaborate split requires its own
  coverage proof; an effective heuristic is not such a proof.
- A component may be eliminated independently only if all its shared
  variables and cross-constraints are represented at the interface. If two
  pieces share a hidden variable, joining after separately eliminating it
  can allow incompatible witnesses. The existing
  [composition theorem](../Formal/BoundaryComposition.lean) assumes the
  needed factorization; it does not discover that factorization.
- Memoization needs an exact semantic key or a proved sound canonical form.
  Variable renamings must preserve constants and shared identities, with maps
  retained for witness reconstruction. Hashes can index exact comparisons;
  an unchecked hash equality is not a mathematical equivalence proof.
- A fast cache lookup does not bound the number of distinct cache states.
  If that number is exponential, memoization has not established a
  polynomial total.

## 5. What a future polynomial-time theorem would contain

For a future, fixed, fully specified deterministic procedure `A_hybrid`, the target
is a bound of the form

\[
\forall I\in\mathcal I:\quad
 A_{\rm hybrid}(I)=\mathbf1_{H}(I)
 \quad\land\quad
 T_{A_{\rm hybrid}}(I)\le C(N(I)+1)^k,
\]

where `C,k` are fixed constants and `I` ranges over all encoded inputs in the
claimed language. Invalid encodings have the agreed parser behavior. If the
language contains the NP-complete reference problem above, this theorem would
establish `P = NP` by the reduction argument in [C].

The existing enumerator does not meet this polynomial target, by Section 3.
For a changed method, separately bound:

1. Parsing, input normalization, and every preprocessing stage.
2. The number of search states, recursive calls, rule applications, or
   iterations, including repeated work and failed choices.
3. The number and bit length of intermediate constraints, circuit nodes,
   basis rows, and stored cache entries.
4. The bit cost of each operation on those objects.
5. SAT witness recovery and verification, and the entire UNSAT computation.

A bound `f(r) N^c` is a parameterized guarantee. It is a general polynomial
bound only if `f(r(I))` is bounded by one fixed polynomial in `N(I)` for every
input in scope. Merely writing the exponential part in a parameter does not
remove it. Similarly, a family of bounds with an input-dependent exponent
`N^{k(I)}` is not a fixed polynomial bound.

For branching, a recurrence such as `T(r) ≤ 2 T(r-1) + poly(N)` proves an
exponential upper bound. A polynomial conclusion would require a stronger
argument, such as a polynomial bound on the total distinct semantic states,
or a different algorithm whose global cost is provably polynomial. Decreasing
depth or observing repeated states in benchmarks does not supply that bound.

## 6. Experiments that can find a missing assumption

The following families organize validation of the current solver and future
changes. Actual finite results belong in the experiment reports; no new
execution counts are inferred from this checklist.

| Family | What it probes |
|---|---|
| XOR-only consistent and inconsistent systems | Exact agreement with linear semantics and detection of `0 = 1`. |
| Gadget encodings of arbitrary 3CNF into 2-CNF plus three-variable XOR | General coverage even when each separate fragment is tractable. |
| Empty XOR part with arbitrary 3CNF | The simpler unrestricted-CNF coverage check. |
| Nonempty XOR part on fresh variables, with arbitrary 3CNF on the remaining variables | Prevents a superficial “has XOR” restriction from hiding general SAT. |
| An underdetermined XOR system whose free variables are constrained by CNF or gates | Interaction between elimination and nonlinear conditions. |
| Mixed SAT and UNSAT instances with the same dimensions and XOR rank | Whether rank-based reasoning distinguishes linear freedom from nonlinear consistency. |
| Equivalent systems after row operations, variable reordering, and clause reordering | Semantics and canonicalization invariance. |
| Shared-variable components joined before projection | Witness compatibility at interfaces. |
| Small random and deliberately structured instances checked by direct enumeration of original variables | An independent semantic oracle that does not reuse the solver's elimination rules. |
| Exactly-one plus even parity | The all-size `2^(k-1)` iteration obstruction for the current decision scan. |

The independent oracle should evaluate the original equations and original
nonlinear constraints directly. Reusing the same simplifier on both sides can
reproduce the same bug. On SAT instances, also verify the returned witness in
the original input. On UNSAT instances, small exhaustive enumeration is useful;
for proof logging, validate the checker independently while keeping
proof-generation cost in the analysis. The current UNSAT certificate already
contains every rejecting cell, so a fast check relative to that explicit
certificate does not remove its exponential generation cost.

Record mathematical work measures alongside optional wall time: `N`, active
variables, equation count, XOR rank `ρ`, free dimension `d`, observation rank `r`,
nonlinear constraint and literal counts, visited states, branch counts,
unique cache states, maximum
intermediate size, and maximum integer bit length. These measurements help
locate failure modes. They are not substitutes for a universal bound.

## 7. Claim gates

| Stage | Claim that becomes available | Claim still unavailable |
|---|---|---|
| A precise input language and semantics | The implementation's intended decision problem is clear. | Correctness or efficiency. |
| Independent finite tests | Agreement on the tested instances. | Unbounded correctness and asymptotic time. |
| All-input correctness and termination theorem | A correct complete solver in the stated model. | Polynomial time. |
| The current `2^r poly(N)` quotient construction, with `r≤d=n-rank(A)` | A quantified observation-rank guarantee. | A polynomial bound for unrestricted SAT; Section 3 rules it out for this enumeration procedure. |
| The explicit 3SAT-to-2-CNF-plus-XOR gadget | NP-complete coverage and recovery of original satisfying assignments. | Parsimonious model counting or faster solution of the reduced instance. |
| Coverage of general 3SAT plus uniform deterministic polynomial total bit time | `P = NP`, through the stated reduction. | This final gate has not been established in this project. |

A failure of our hybrid procedure is an algorithm-specific obstruction. To
establish `P ≠ NP`, a separate argument must cover every deterministic
polynomial-time candidate, as quantified in
[solution_criteria.md](solution_criteria.md#5-what-the-opposite-direction-would-have-to-prove).

## References and status

- **[C]** Stephen Cook, [*The P versus NP Problem*](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf), official Clay Mathematics Institute problem description. Definitions and Proposition 1(c) provide the class and reduction criterion used here.
- **[APT]** Bengt Aspvall, Michael F. Plass, Robert Endre Tarjan, [*A linear-time algorithm for testing the truth of certain quantified boolean formulas*](https://doi.org/10.1016/0020-0190%2879%2990002-4), Information Processing Letters **8**(3), 121–123 (1979). [Author-institution publication record](https://collaborate.princeton.edu/en/publications/a-linear-time-algorithm-for-testing-the-truth-of-certain-quantifi/).
- Existing controls: [affine systems](affine_projection.md),
  [parity representations](parity_projection.md), and
  [fixed-palette star projection](projection_barrier.md).

The current solver supplies exact semantics, a parameterized upper bound, and
an explicit algorithm-specific worst-case obstruction. The rule contracts and
polynomial target describe obligations for future changes. Neither the
abstract Lean theorem nor finite Python checks claim an end-to-end formal
verification or a resolution of P versus NP.
