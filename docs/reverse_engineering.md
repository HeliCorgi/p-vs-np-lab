# Working backward from the solution criterion: XOR plus nonlinear constraints

## Phase 18: retire the high-digit search on the existing expanding family

We tested the precise [phase-17 high-digit question](feedback_simulation.md).
On the phase-16 proper ternary clause expanders the new answer is negative
independently of digit, modulus, coefficient size and number of learned
rows: [common semantic support](support_localization.md) makes each small
scope's integer affine lattice the entire ambient lattice even after
bounded-width resolution. Coordinate two-faces extend this conclusion to
multilinear moment coordinates of degree at most two. The semantic support
need not be the raw ancestors of the displayed proof.

The [variable-query tree bound](conditional_localization.md) is stronger
than failure after one pin: absorb a maximal small set of clauses around
free questions and keep enough expansion for the remaining restricted
integer leaves. Hall matching permits both answers to fresh queries.
With fixed width and scope, an exponential number of tree leaves is
necessary. No theorem here prohibits shared intermediate proofs in a DAG.

A [different expander construction](field_split_boundary.md) enters the
alternative direction. A two-characteristic flow switch has a polynomially
discoverable one-split proof, while ordinary PC needs high degree in every
field and the unpinned one-sum system fails for any detecting digit by
[signed integral marginals](coprime_pseudomarginals.md). Its expanding graph
is the graph carrying flow, **not** the clause-variable graph of the first
family. One selector with incompatible Boolean residues already illustrates
why a domain-aware bridge can also solve it; the previous unary bridge
refutes the finite UNSAT controls. The two-prime construction and the
all-field restriction argument have explicit antecedents in Lichter–Pago
and Conneryd–Ghannane–Pang; this cycle checks the lab's precise encoding.

**Next acceptance test.** Do not continue increasing a modulus, variable
tree depth, or the number of switch benchmarks. Specify an inference outside
the proved tree model. For example, allow a query of a parity of many
original variables, and specify exactly how a conditional leaf may use that
parity (never as an unchecked new axiom). Either show how to adapt the
absorption/extension argument against that explicitly defined rule, or give a
polynomial-size family separation with an independently verifiable certificate
and a polynomial discovery bound. For shared proofs, charge the cost of
establishing the same learned clause under all incoming contexts. Encoding
an arbitrary SAT decision into a question or an unchecked merger is not an
algorithm. Other all-field-degree-hard families might still have high-digit
one-sum proofs; neither phase 18 family supplies such a positive example.

## Phase 17 decision: a real separation for feedback, and a degree bound for the combination

The [audited research program](research_program.md) records the starting
commit, earlier failed routes, and the standards for a solution claim.
The previous positive gate is met by [shielded parity on graphs](feedback_separation.md):
one-pass path learning and arithmetic decide both charge parities, including
SAT witness recovery, with polynomial total bit cost on that family when
budgets scale with the explicit input. Ordinary resolution on odd expanding
graphs needs exponential length; all raw integer affine scopes of size at
most 15 are blind. This comparison does not extend to all-field PC: the
positive family is easy in its matching characteristic. The [carry
control](feedback_carry.md) separately needs more than a prime-field *linear*
test; it is not the expander resolution separation.

More strongly, a [simulation theorem](feedback_simulation.md) applies to
any width-bounded resolution prefix followed by bounded-scope integer
leaves and one weighted global contradiction. In a detecting characteristic
$p$, the degree bound involves the width, local scope, and the index
$D=p^{v_p(R)}$ of the first nonzero digit of the integer right-hand side.
For a squarefree modulus one can take $D=1$. Thus the earlier family with
linear PC degree in **all fields** obstructs the entire combination when
these three parameters are small. The theorem does not imply proof-size
hardness for arbitrary binary-encoded moduli, or transfer to several rounds,
branching on arithmetic, or additional extension variables.

**Next test.** On a family with an independent all-field degree lower bound,
either find a polynomial-cost high-digit arithmetic refutation with small
prefix width and leaf scope, or prove a further obstruction. Include how
the necessary digit and certificate are discovered from the original CNF.
Inflating weights or a modulus on an already easy carry cycle will not meet
the gate. A separate possible direction is a split between different
characteristics; this lies outside the theorem and needs a separate
encoding and lower-bound proof. No additional benchmark of the same
one-way shielding is needed merely to enlarge the variable count.

## Phase 16 decision: the nonlinear finite gate is passed; expose the hybrid boundary next

The [previous 31-variable/152-clause blind core](correlation_proof_boundary.md)
now has an independently checked refutation found from its raw clauses.
Its minimum ordinary-resolution width is exactly four. Exact join/project
reasoning needs union width five, polynomial calculus needs degree five
over every field, and the explicitly defined local-distribution hierarchy
first becomes infeasible at level five. The two latter executable checks
are an F2 arithmetic proof and rational level-four distributions, respectively;
the all-field and level-five implications are proved in the accompanying note.

The first learned binary clause has a full integer affine lattice, so
immediately replacing it by that lattice would discard the recovered
information. Global learned relations and their complete derivations must
be retained. The 368-node refutation also hides a larger discovery process:
26,826 stored clauses, 180,420 candidate pairs, and over eight million
superset containment checks. Both proof size and discovery are recorded.

The [same-class asymptotic control](correlation_proof_boundary.md#4-a-scalable-control-in-the-same-proper-linear-3-cnf-class)
constructs proper linear 3-CNF families with raw integer-blind small fragments
and polynomial-calculus degree Omega(n) over every field, using a published
boundary-expansion lower bound. It also forces linear resolution and
exact-join width. Increasing fixed caps is therefore not a completeness
argument for these systems. The construction is existential, not a practical
large-instance generator or a lower bound against every SAT algorithm.

**Next test and acceptance gate.** Specify and implement the feedback
between proof-certified nonlinear consequences and the global integer
backend. Seek an infinite family on which the combination has a proved
advantage over either stage alone, and a precise accounting of discovery,
local truth tables, integer coefficient bits, and all learned definitions.
An integer-lemma inference is not an ordinary resolution step; do not
silently transfer resolution or PC lower bounds to that enlarged system.
Conversely, a finite success of the hybrid does not prove a polynomial
bound on every 3SAT input. Require the family theorem and the proof-system
comparison before spending more effort on larger undirected searches.

## Phase 15 decision: global integer obstructions work; arithmetic-only completeness does not

The previous target is now implemented. The [integer backend](integer_hull.md) derives exact equations and congruences from raw Boolean tables, combines them without a supplied modulus, and emits a separately checked contradiction. [Carry loops](global_integer_fixtures.md) have torsion-free local tables but globally impose m*x=q; the raw tests recover 4, 5, 7, 8, 9, 25 and 49. The composite examples distinguish integer solvability from checking every prime field separately. They do **not** separate this backend from the previous Boolean field bridge, which already refutes its recorded carry-loop controls.

[Conditional integer proofs](integer_probe.md) also refute a guarded disjunction whose root pass finds no local equation. This is a useful instance of established failed-value inference with an arithmetic oracle. It does not remove the main barrier: [the full integer-lattice argument](global_integer_theory.md) shows that the existing Hall-expansion class defeats every raw local affine congruence, every modulus, and singleton probing with such an oracle. The scope of that theorem excludes arbitrary representation-changing preprocessing.

The [prior-work review](global_integer_theory.md#5-what-prior-research-already-settles) gives a further stop sign: the Lichter–Pago ICALP 2025 result, updated in January 2026, rules out several stronger integer/LP relaxation schemes as universal algorithms even for tractable CSP templates. Neither more primes, larger constant tables, nor simply appending an LP is a justified route to universal completeness.

**Next test and acceptance gate.** Move the main search from arithmetic completeness to the information discarded by affine projection: compatibility of *actual local Boolean words* across overlaps and alternatives. Use the fixed, independently refuted 31-variable/152-clause Hall-blind input and its satisfiable same-support sibling as the first regression, not another flow family. A candidate inference must produce a nonlinear consequence or a checked global case cover that actually distinguishes them. Before scaling it, identify its established proof-system counterpart and the relevant published lower bounds. Count the cost of discovering and storing overlap correlations, added coordinates, case covers, and integer coefficients in the **original** encoding length. Merely re-encoding each clause as a cubic polynomial, adding nonnegative integer local weights, or allowing unrestricted branching restores an equivalent hard problem and does not meet the gate. A finite success is only a starting point; a P=NP claim still requires a fixed polynomial all-input bound and completeness, and a P≠NP claim cannot rest on a lower bound for one chosen proof system.

## Phase 14: hidden conservation laws, with an explicit stopping point

The [ternary solver](trit_solver.md) finds field structure in signed, permuted raw width-three clauses, solves the recognized affine family, and checks a witness or a modular refutation. [Field bridges](mixed_modular.md) certify contradictions invisible to independent F2/F3 runs. [Local rank](prime_spectrum.md) and [integer invariants](local_torsion.md) give evidence for the choice of arithmetic. Changing primes alone is not a universal strategy even on flows: [the finite-abelian classification](abelian_visibility.md) explains why an imbalance in the common kernel of all field characters survives every local prime-field row and every subsequent sound bridge between those rows. [Native order-four arithmetic](cyclic_four.md) resolves one such case. Separately, the [expansion barrier](modular_barrier.md) demonstrates an NP-complete fixed-locality blind class, and existential SAT/UNSAT twins retain full affine and quadratic spans on all raw fragments up to a linear size.

**Next test:** do not add one solver per modulus. Seek an algorithm detecting *global* integer obstructions: derive a presentation from independently checkable local Boolean relations, then combine rows and certify a contradictory congruence without being supplied its modulus. An instructive test must include an obstruction appearing only after combining local tables whose individual integer invariants are trivial (the odd cycle is the first control), as well as the hidden order-four and mixed cases. State exactly which integer or modular relaxation is solved and charge the bit length of coefficients, auxiliary values and proof. The expansion class still precludes claiming that combinations of raw local degree-one or degree-two consequences alone solve unrestricted 3SAT.

## Phase 13 decision: move the main search beyond resolution-only model transport

[Derived witness transport](derived_transport.md) defeated the [previous tag-width obstruction](interface_transport.md), and [verified recovery](blind_recovery.md) undid the exact distinct-support presentation on proper 3-CNF images. The stronger [two-way resolution barrier](robust_ceiling.md) and [all tag layers construction](layered_resolution_barrier.md) show why merely increasing the search budget for syntactically justified signed substitutions cannot supply a general polynomial-width, polynomial-proof program. These are existence results about specified proof formats, not an explicit hard instance for every algorithm. Fixed-depth propagation is only one such format. A [one-bit case/parity proof](case_parity.md) handles those modular obstructions without forming all the residuals.

**Next research target.** Test how a solver can recover algebraic structure from raw clauses when ordinary resolution is the wrong proof language. A specific falsifiable benchmark is to replace binary parity with a conserved sum modulo three, encoded over Boolean variables, and independently permute/negate variables and hide the local relations with satisfiability-preserving gadgets. Seek an algorithm which identifies the participating coordinates and common equation, emits a raw-CNF-checkable proof, and has a family-wide worst-case bound including discovery. Include satisfiable siblings that differ in total charge and controls mixing binary and ternary-modulus constraints. Such a result would be progress on representation and proof discovery; P=NP still requires a bound on **every** unrestricted input or some entirely different all-input argument.

## Current checkpoint: certify domination, or refute many branches at once

The [direct substitution checker](transport_discovery.md) gives an inexpensive sufficient condition for discarding a branch and can transport a particular witness. It solves the [previous capped counterexamples](transport_positive.md). Its discovery problem is NP-complete without restrictions. Worse, the [explicit minimally unsatisfiable antichain](transport_obstruction.md) shows that even unlimited search for the specified raw certificates cannot give a universal width bound. This is independent of complexity conjectures.

A complementary constructive target is to derive **one unconditional consequence covering many cases**. [The implemented one-bit split rule](split_parity.md) finds common affine consequences without crossing all cases. [Private resolution](private_resolution.md) recovers the necessary consequences on one [padded family](transport_padding.md); another NP-complete image makes both of these root passes completely silent. The distinction matters: the negative results for raw transports and for root passes cannot simply be multiplied or extrapolated into a lower bound on unrestricted SAT or on every combined driver.

The next falsifiable test is to produce checked non-affine consequences or substitutions justified by *derived* clauses on the distinct-support reduction, where no starting parity/sign orbit or eligible private pivot exists. A first candidate is to use resolution or unit propagation to justify a proposed pulled-back target clause, charging both the search and the proof length. Before treating this as a path to P=NP, require a polynomial all-input bound (in the original encoding length) on retained branches and the total cost of finding and checking these justifications. The immediate goal is a family-wide positive theorem and a control that separates it from existing methods, not a score increase based on successful small inputs.

## Main target: polynomial list width of unrestricted SAT self-reduction

[The decision-pruning criterion](decision_pruning.md) replaces the previous goal of deriving pairwise parity conflicts. The [matching twins](parity_shadow.md) show exactly which information every proper linear feasibility observation misses. A sound collision label for anchored disjunctions, computable in polynomial time and of uniformly polynomial diversity at satisfiable anchors, would decide 3SAT in polynomial time. We constructed [positive and negative controls for actual labels](codec_controls.md), including [a stronger simplifier and a new obstruction](blocked_pruning.md). The missing all-input bound is explicit; none of these counterexamples lower-bounds arbitrary SAT solvers.

## Previous target: decide many coupled parity conditions without listing every small seed

We now [compile the residual affine fiber](../src/pnp_lab/fiber_arrangement.py) into forbidden intersections of parity equations. The [compact clause encoding](selector_overlap.md) needs just one private bit and two forbidden codimension-two flats per 3-literal clause. Thus a deterministic method deciding avoidance in polynomial time on every such image would decide 3SAT in polynomial time. A satisfiability witness projects back to the original clauses. Bounded-degree [static proofs](overlap_refutation.md) cannot be complete here, and [bit elimination](event_projection.md) has an explicit bad cut in its union-of-flats representation.

The [observation solver](observation_2sat.md) instead solves a 2-CNF relaxation and imposes its remaining independent parity checks. It is polynomial for each fixed number of checks, but general inputs can force many of them. A concrete next target is to derive conflicts **between parity checks** from the implication graph before enumerating their seeds: on the [connected colored family](observation_limits.md) two classes exclude all joint choices even though either class is separately feasible. A useful first result would be a sound, independently checkable rule that detects that family for all sizes, followed by hard controls with no conflicting pair of checks. Such a rule, even if successful, would not yet imply a uniform polynomial worst-case bound on all compact 3SAT images.

## Previous target: feasibility in a fiber with several holes

A choice from a ternary support becomes an affine plane with one forbidden point. [Symbolic addition](hole_flats.md) can combine certain intersecting planes without materializing their sums, even when their differences are not graphic. [Graph realization](graphic_gauge.md) and [fixed-coordinate branching](gauge_matching.md) provide complementary solvers. Polynomial work on successfully recognized families does not bound the complete fallback. [Every labelled binary column matroid can occur as a minor](binary_minor_universality.md) after exact affine absorption on some sparse bridge image, so no proper minor-closed binary class covers every image. A remaining target is joint feasibility when the individual direction spaces have trivial pairwise intersections but collectively have dependencies: find a decomposition of the target that simultaneously avoids each forbidden point, or prove none exists. A polynomial all-input algorithm for these residual 3SAT images would suffice for P=NP.


## Current target: three options of weight two

The [support threshold](support_threshold.md) reduces every 3SAT instance to a zero-target XOR selection with at most three options per group, each option touching at most two coordinates, and exactly two groups incident to each coordinate. The binary-choice and unit-weight edges have polynomial solvers. The [explicit frontier](affine_frontier.md) decides general supports, but it does not yield the missing general polynomial bound. Its all-orders grid obstruction concerns the earlier five-option bridge, not this smaller encoding.

A concrete normal form for the remaining case: translate any three-point support `{a,b,c}` by `a`. Choose selector bits `y,z` for the contributions `b XOR a` and `c XOR a`, forbidding only `y=z=1`. The target shifts by the XOR of the anchors. Binary supports need one unrestricted selector; singletons contribute constants; an empty support is immediately impossible. This gives linear equations plus disjoint forbidden pairs. It is an exact decision equivalence, not yet a polynomial algorithm. Symbolic methods that avoid storing every reachable sum must still prove polynomial bit cost for construction, composition, and the final feasibility query.


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

**Stage 4 follow-up:** [joint XOR-plus-binary-clause inference](joint_reasoning.md)
now recovers the bridge's source clauses and refutes the encoded odd-cycle
family before enumeration. Its fixed width-three, one-pass discovery and
independent certificates do not make the entire solver polynomial: exactly-two
plus odd parity and the documented connected ternary Tseitin family still
force exponential enumeration in this implementation. These are obstructions
for the stated rules, not for unrestricted joint reasoning or other solvers.

The separate [group-signature counter](signature_counting.md) reuses the finite
measurement/fiber identity inspected in `openai/math`. Its total cost includes
local truth-table construction and signature convolution. A polynomial route
would require an efficiently found valid decomposition for **every** input
and polynomial bounds on both these costs, including all intermediate tables
and integer bit operations. The identity map shows that explicit signatures
can retain all `2^b` local assignments. Recognizing favorable examples alone
does not prove that every 3SAT input admits favorable structure.

The [constant-block bridge](constant_block_bridge.md) sharpens this obligation:
general 3SAT reduces to group-local binary CNF with groups of size at most
five and mutually disjoint ternary XOR rows. Consequently local construction
can be bounded by 32 assignment visits per group; NP-complete coverage remains
in the global combination of those small tables. A uniform polynomial join
algorithm for all instances in this restricted image would already yield
`P = NP`. This is a reduction criterion, not a proof that polynomial joining
is impossible. The current counter still has an exponential-state example
even on easily factored disjoint clauses, so its stored-state growth must not
be attributed to every algorithm for that family.

[The current ETH releases](prior_work.md) supply a separate claimed
subexponential upper bound, not a polynomial one. The upstream theorem's
machine/input semantics and our actual verification scope are recorded in
[the formal audit](eth_formal_audit.md); a successful build of a formal
statement would not automatically certify a sharper paper statement.

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
