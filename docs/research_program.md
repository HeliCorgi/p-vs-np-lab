# Research objective and audited starting point

**Goal:** a complete mathematical proof of P=NP or P≠NP. **Status:** open.
On 2026-11-07 JST the user also accepted approximate empirical tendencies
as a deliverable. This adds a separate experimental track; it does not
weaken the requirements for a complete proof or supply probabilities of
either complexity-class relation.
The [solution criteria](solution_criteria.md) specify the quantifiers; Clay's
[official listing](https://www.claymath.org/millennium/p-vs-np/) still marks
the problem unsolved (checked 2026-11-05 JST). The repository is a research
record. Its phase numbers measure completed investigations, not proximity
to a Millennium Prize solution.

## Current continuation: reconstruct one proof and test one alteration (2026-11-11 JST)

The user approved a strategy change: pause direct general-lower-bound
attacks, understand an existing proof thoroughly, and examine one change.
We selected McKay–Murray–Williams (2019), Sections 2.1, 3 and 5. The
[worked reconstruction](mcsp_merge_reconstruction.md) traces the interval
merge invariant, coherent witness selection, the use of NP contained in
P/poly, and the resulting coarse circuit bounds. A binary tree suffices
for that endpoint; we do not claim the paper's sharper uniform bounds.

The selected alteration uses standard hash isolation to replace canonical
Sigma_3^P output-bit queries by two rounds of Sigma_2^P queries: parallel
candidate bits, then coNP verification of the assembled candidates. For
m-bit merge inputs and L-bit witnesses, a fixed family of
16(L+1)(m+1) affine hashes exists that isolates a witness for every feasible
input of that length. The isolation probability and the union bound over
all inputs are proved explicitly; the advice is independent of the actual
truth table.

The tradeoff is essential: this family is fixed by a nonuniform existence
argument, without a polynomial-time construction, and local overhead is
only bounded polynomially. Sigma_2^P queries remain unsolved computations.
The same coarse conditional N·poly(n)-size, poly(n)-depth upper bound
follows under NP contained in P/poly, but no stronger lower bound or weaker
fundamental assumption has been obtained. This is a proof-study result
using standard tools, with no novelty claim.

The finite audit checks exact isolation probabilities for all 273 nonempty
witness sets on up to three bits. For the 14 functions computable by
two-input circuits with at most two gates, it checks all 81 partial tables
using a fixed 3,168-hash family and all 196 child-representative pairs.
Postverification rejects 5,308 candidate strings, including 5,132 malformed
circuits and 42 circuits with wrong constrained values. These finite
checks validate the selection mechanism, not a general efficient merge
algorithm. The script is embedded in the study note; solver, result-manifest
and Lean sources are unchanged.

Retain the explicit invariant and resource accounting as the baseline for
further study of this same proof. Lowering the oracle alternation alone is
not adopted as a new main route to P vs NP. There is still no new proof
candidate for the full problem.

## Previous continuation: requested general lower bound remains unproved (2026-11-10 JST)

The user explicitly asked to prove the general search-MCSP circuit lower
bound. **We have not proved it.** The target remains the exclusion, for
every fixed c, of size 2^n n^c and depth n^c circuits at infinitely many
lengths. The previously checked magnification theorem would turn that
result into NP not contained in P/poly and hence P≠NP. The linear bound
from the previous continuation is not sufficient.

We attempted an [algebraic rank argument](solution_criteria.md#15-requested-general-search-mcsp-lower-bound-the-rank-attempt-fails)
using compression to a short circuit description followed by evaluation.
Correctness at zero and every unit table makes the Boolean multilinear
linear part of this composition have rank N. Applying the ordinary chain
rule to factor that matrix through the short description is invalid:
Boolean reduction T_i²=T_i need not preserve formal derivatives.

An explicit four-bit example compresses zero and the unit tables into
three bits and decodes them correctly. The formal composition has
Jacobian rank one at zero; its multilinear reduction has rank four.
Exact polynomial arithmetic checked both matrices and all 16 inputs.
Retaining all nonlinear code features repairs the factorization but
gives only N<=2^r-1, a description-length bound attained by the singleton
encoder. It supplies no size lower bound for computing that code.

The attempted contradiction did not use the encoder's size or depth;
it would have excluded even the finite exhaustive-search function.
This is a useful check on its failure, not progress past the general
circuit barrier. Stop this rank argument. There is no new complete-proof
candidate, general superlinear lower bound, or Lean theorem. The exact
countercheck is embedded in the existing solution-criteria document;
solver and result-manifest sources are unchanged.

## Previous continuation: test a circuit lower-bound mechanism (2026-11-10 JST)

We continued the circuit search-MCSP target from the previous investigation.
The [dependence and reconstruction audit](solution_criteria.md#14-continuing-the-circuit-target-essential-inputs-and-sparse-reconstruction)
tests whether many forced changes of the output circuit imply the required
search-circuit lower bound. They do not supply that inference.

The zero table and its one-bit perturbations force every input bit to affect
the output. For a fan-in-two circuit with N inputs, G gates, r output bits
and depth d, this gives G>=N-r and r·2^d>=N. These are compatible with
the N·poly(log N) size and poly(log N) depth that must be excluded. In fact,
a shared tree encodes every singleton table with exactly 2N-log2(N)-2 OR
gates. Charging all output dependencies separately would count shared work
more than once.

The stronger sparse-family attempt also fails: for n-variable tables with
at most floor(n/2) ones, a fixed bitonic sorting network finds all active
addresses with O(N n³) Boolean gates and O(n²) depth. A fixed template
converts those addresses into a circuit with at most n² gates. This works
for 2^(Omega(n²)) distinct functions, so the large number of outputs does
not force the target bound. It extends to a small Hamming neighborhood of
any **given** sufficiently small circuit, including dense functions.
The cost of producing its reference truth table is included. Finding an
unknown reference circuit is not assumed available.

The finite audit checks 515 singleton cases and 68,674 sorting inputs,
including all truth tables on 2, 3 and 4 variables. It checks record
permutations and contents independently, then evaluates 2,889 reconstructed
circuits and another 345 circuits from the dense-center extension on all
original assignments. Exact gate-count and depth bounds pass. The general
constructions and limited lower bound are mathematical arguments, not
extrapolations from these checks.

Stop this dependence/counting-based attempt at magnification. The sparse
compressor is a promise algorithm: overflow does not establish that no
small circuit exists. The general search-MCSP lower bound remains unproved,
and this continuation produces no new complete-proof candidate or evidence
favoring P=NP or P≠NP. It uses standard circuit and sorting constructions;
no novelty is claimed. The reproduction is embedded in the existing
solution-criteria document. No solver, result manifest or Lean source changed.

## Previous continuation: investigate different mechanisms (2026-11-10 JST)

The user asked for other methods. We checked original sources for two
different connections: holographic algorithms toward P=NP, and circuit
hardness magnification toward P≠NP. The [candidate audit](solution_criteria.md#13-alternative-mechanisms-holographic-algorithms-and-circuit-magnification)
records the exact transformations, literature endpoints and reproduction.
These are known research directions; no novelty is claimed for them.

For the algorithmic route, representing #SAT by a polynomial-size planar
matchgate network with controlled construction and arithmetic costs would
provide a polynomial SAT algorithm. We tried a common invertible basis on
all variable edges and its dual on all clause edges. A direct calculation
using the known matchgate parity condition proves that ternary equality
and ternary OR cannot both become matchgate signatures under **any complex
basis of this form**. An independent planarization check also fails: the
unsigned crossing has residual 2 in a matchgate identity. The known signed
crossing is a different counting tensor. Counting modulo 2 cannot by itself
distinguish a satisfiable formula with two solutions from an unsatisfiable
one. Stop these particular local constructions; global transformations and
other exact algorithms are not excluded.

Exact rational checks passed for all 496 invertible matrices with entries
from -2 to 2, including contraction preservation. All 256 ordered-pair
matchgate identities were checked for each of the unsigned and signed
crossing tensors. The finite checks audit the conventions; the complex-basis
claim rests on the symbolic argument, not the finite sample.

Retain as a next research target the **circuit**, rather than memory-only,
version of search-MCSP magnification. On an N=2^n-bit explicit truth table,
find a circuit with at most n² gates when one exists. Showing that this
search has no N·poly(n)-size, poly(n)-depth general Boolean circuit family
would imply NP not contained in P/poly and hence P≠NP, by
McKay–Murray–Williams (2019), Theorem 1.4, third bullet. We rechecked both
the theorem and its oracle-replacement proof. A lower bound only against
O(log N) depth gives a different, insufficient endpoint.

The same paper's short-oracle construction supplies a useful first filter:
a method that would prove the target even with arbitrary poly(n)-input
functions as unit-cost gates cannot work. Such an oracle circuit already
exists within the budget. This identifies a requirement on the missing
technique, not a technique that meets it. The actual search-circuit lower
bound is **unproved**, and we have no new complete-proof candidate. The
previously pruned streaming prefix-counting argument is not revived.

Only research documents changed. The check code is embedded in the existing
solution-criteria document; no executable-source manifest, solver, result
report or Lean theorem was changed. No numerical tendency between P=NP and
P≠NP follows from the candidate's failure or from the literature survey.

## Previous continuation: try a polynomial SAT shrinker (2026-11-10 JST)

After parking canonical hard tables, the user asked to continue. We changed
to the P=NP direction and tested exact Davis-Putnam elimination with a
nonincreasing clause budget. Trial blocks contain one or two variables; a
pair may grow after its first elimination as long as the final clause count
does not increase. Tautologies, duplicates and subsumed clauses are removed.
The [cost and progress audit](solution_criteria.md#12-a-pnp-attempt-bounded-clause-elimination-and-two-variable-lookahead)
proves that these trials, intermediate representations and accepted rounds
would have polynomial total bit cost if every nonterminal CNF had a suitable
block. That progress claim is false.

For every p>=11, the explicit connected family has variables A_i,B_i,C_i and
the 6p clauses on A_i,B_(i+t),C_(i+2t), with t=0,...,5 modulo p. The first
three layers are positive and the other three negative. Every variable has
three occurrences of each sign and every pair of clauses shares at most one
variable. Every single elimination adds exactly three clauses and eighteen
literal occurrences. Eliminating any pair adds six clauses if the variables
share no clause and ten if they do. These counts hold after full duplicate,
tautology and subset simplification, in either elimination order. The proof
accounts for possible overlap among the pair's final resolvents.

The family is SAT: A=true and B=false works with any C. Thus it refutes this
particular preprocessing progress claim on easy instances, not P=NP or all
SAT algorithms. Other transformations, larger blocks and different resource
budgets are not ruled out. This does not restart the earlier affine-union
representation branch; the tested objects here are ordinary CNF clauses.

The local increase alone does not imply superpolynomial total growth. We
therefore checked a more permissive budget separately: any UNSAT run that
only explicitly generates ordinary resolvents until obtaining the empty
clause yields a resolution refutation of size at most its total generated
lines plus the input clauses. The known expander-Tseitin resolution lower
bound, rechecked against Ben-Sasson–Wigderson (2001), rules out a polynomial
total-cost general SAT algorithm restricted to this mechanism, independent
of elimination order or grouping. This closes a budget-only repair; it does
not cover stronger inference systems or semantic decision rules. It is an
application of an existing result already cited in the repository.

Independent semantic checks passed on 259 small formulas and 1,295 projected
assignments. At p=11,13,17, including two signed/permuted variants per size,
369 single eliminations and 7,632 pairs checked in both orders matched the
all-size formulas. The reproduction code is in the existing solution-criteria
document. No asymptotic claim is inferred from finite growth curves.

Stop this candidate, its two-variable repair and a budget-only repair within
ordinary resolution before building a new general solver. No executable
source, result manifest or Lean proof changed. Other shrinking methods are
not excluded; the P=NP route has no surviving complete-proof candidate from
this attempt.

## Previous continuation: test bit certificates and park canonical selection (2026-11-10 JST)

The user asked to continue the missing bit-verification step. We tested
certificates consisting of a small collection of values of the selected
function. The [interpolation argument](solution_criteria.md#11-bit-certificates-sample-interpolation-and-canonical-soundness)
constructs a circuit of at most 2mr gates fitting any r consistently labeled
m-bit points. Thus a sample-only certificate excluding all size-s circuits
needs r>s/(2m). With literal m-bit addresses and labels, its length exceeds
s/2. This mechanism therefore cannot amplify the lower-bound exponent
relative to the cost of reading the certificate. The scope is explicit
samples, not every possible NP proof or compressed certificate.

We also tested the tempting replacement that certifies some hard table and
its requested bit. Counting already implies that, in the intended range,
hard tables exist with either value at every position. Such a verifier accepts
every position, including zeros of the selected table. At three inputs and
three gates, `00000110` is the first hard table but `10000001` is also hard
and has the opposite first bit. Even a perfect hardness check on the latter
does not certify a bit of the former. Canonical consistency cannot be omitted.

The general interpolation construction was executed on all 6,651 partial
truth tables up to three inputs, checking 35,220 prescribed values and the
gate bounds. The false-bit example was checked against the exact circuit
catalog. Reproduction code is in the existing solution-criteria document;
these checks do not prove general NP hardness or a new asymptotic lower bound.

Park the canonical-hard-table branch as a main route under the user's
early-pruning instruction. It has produced no sound bit verifier with the
needed cost advantage. This decision does not assert that all bit certificates
are impossible. Retain the constructions and the exact stopping conditions;
do not reopen the branch by assuming its missing verification step. No new
complete-proof candidate, executable source, result manifest or Lean proof
was added in this continuation.

## Previous continuation: count hard decision tables and charge their selection (2026-11-10 JST)

The user asked to continue. The [direct counting attempt](solution_criteria.md#10-continuation-construct-the-hard-decision-function-by-counting)
defines the decision predicate that a partial truth table extends to a
function requiring more than s gates. If a table has N=2^m entries and at
most 2^ell easy tables exist, every r-bit prefix has a hard completion when
N-r>ell. With polynomial s and r in m, the proposed predicate is therefore
constant YES at large lengths. This explicitly tests the decision function,
without inferring hardness from the complexity of a verifier.

We repaired the consistency problem by selecting the lexicographically first
hard table and asking for one of its bits. A second repair actually shortens
its representation: among the first |E|+1 tables one is hard, so the canonical
table consists of zeros followed by at most ell+1 bits. At a fixed budget
s=m^k this is polynomial length. A multiplexer construction also proves
`C(D_m) <= 8t+m` for a t-bit tail. Thus any hard tail at s>=2m needs more than
s/16 bits, and processing the whole tail cannot supply the needed exponent
ratio. Each fixed-k bit language is in P/poly unconditionally.

The remaining hardness check has quantifiers `forall small circuits C,
exists input x witnessing disagreement`. Tail-prefix search adds an outer
existential quantifier; greedy canonical selection therefore gives a
P^(Sigma_3^P) upper bound for fixed k. It gives no NP verifier for a selected
bit. Under P=NP each fixed-k construction would be in P, with its polynomial
degree allowed to depend on k. No impossibility of a different NP certificate
is asserted. The short-tail repair removes one description-size obstruction,
but does not prove the required membership or exponent amplification.

The cost analysis also proves compatibility with the opposite assumption:
under P=NP, padded hard-completion queries can be decided in polynomial time
in N. Greedy selection then constructs, in time 2^O(m), a language whose
length-m functions require more than 2^floor(m/2) gates eventually. This places
the constructed language in E under that assumption, not NP, and gives no
contradiction. Padding the original input to the truth-table length makes this
particular lower bound only square-root in that new length. These are elementary
counting/selection deductions with no novelty claim.

The small control exhaustively classified all circuits on three inputs with
budgets zero through three. Semantic DAG enumeration agreed with independent
raw gate-sequence enumeration, and 2,044 budget/prefix pairs were classified.
There are respectively 5, 14, 40 and 84 easy truth tables among 256. The
complete counts and reproduction snippet are in the existing solution-criteria
document. Independently, all 546 short-tail circuits at up to three inputs
were constructed and their 4,212 truth-table rows and gate counts checked.
No asymptotic conclusion is extrapolated from these counts; the tail bound
has a separate all-size construction and proof.

Stop these constructions as NP lower-bound proofs. Their specific missing
step is an NP verification of the selected hard bit function with the required
cost, not existence of a hard table. No executable source, result manifest or
Lean source changed; no new complete-proof candidate was obtained.

## Previous continuation: test the first existential amplification (2026-11-10 JST)

The user asked to continue the backward proof attempt. The
[continuation](solution_criteria.md#9-continuation-test-whether-existential-witnesses-amplify-the-lower-bound)
first checks the converse of the previous implication: NP not contained in
P/poly supplies the unbounded-ratio family simply by taking the same SAT
language at every index. Thus that condition is equivalent to this stronger
circuit separation target. It specifies the needed quantitative transfer;
it has not reduced the difficult part to a separately proved theorem.

We then tried to preserve a seed's circuit hardness in a verifier and transfer
it through existential witnesses. For any f(x), the explicit relation
`V(x,z,w) = z AND [w_1=f(x)] AND AND_{i=2}^q NOT w_i` retains f as a restriction,
has exactly one witness on every YES input, and has witness density `2^(-q)`.
Nevertheless its projected decision function is just z, with no gates. Both
YES and NO ordinary inputs occur. For parity and q=n, the verifier uses at
most 6n gates and linear time. The exponentially rare successful witness does
not give a lower bound for deciding its existence.

Pinning w_1 to one or to another cheaply computable function only produces
an explicit small decision circuit. More generally a small successful-witness
selector composes with the verifier to give a small decider, and q witness
bits admit a `2^q`-copy decision circuit. These are proved upper bounds and a
counterexample to the attempted transfer, not new general lower bounds or an
impossibility result for all existential constructions.

An independent bounded check covered every Boolean function on one, two or
three input bits and witness lengths one through four: 1,104 relations,
127,200 verifier rows, 16,960 fibers and 8,480 restriction checks. The
reproducible snippet is in the existing solution-criteria document; it verifies
the finite identities, not the all-size lower-bound claim. The all-size
counterexample and resource bounds have separate paper proofs.

Stop this mechanism and its two repairs. The missing result is still a lower
bound on the projected decision function against unrestricted circuits. No
such bound or complete-proof candidate was obtained. No solver, benchmark
suite, result manifest or Lean source changed in this continuation.

## Previous continuation: construct backward from the missing requirement (2026-11-10 JST)

The user asked to identify what is needed and construct the argument from it.
The [backward proof architecture](solution_criteria.md#8-backward-construction-make-the-hardness-exponent-outrun-the-verification-cost)
now gives a complete conditional transfer argument, with the unresolved lower
bound exposed rather than assumed as a working lemma. It is a sufficient route
through general circuits, stronger than the required uniform separation.

For a family L_k with verification cost O(n^(b_k)) and infinitely-often general
circuit lower bounds Omega(n^(a_k)), an unbounded ratio a_k/b_k suffices to make
one fixed SAT language require superpolynomial circuits. The proof constructs
the near-linear Cook-Levin reductions, charges their circuit and output sizes,
pads outputs to a fixed length, assumes a size-N^d SAT circuit and then chooses
a fixed k with a_k>d b_k. Composition gives size n^(d b_k+o(1)), contradicting
that L_k's bound. This repairs the previous quantifier transfer only under the
additional quantitative condition; that condition has not been established.

A concrete seed, parity, has a linear verifier and a general-circuit lower
bound of n-1 gates. An effective operation that repeatedly increases the ratio
by a fixed factor rho>1 would therefore finish the chosen route. We tried
padding, independent conjunction and connected graph-parity constraints as
candidate operations. Padding cannot improve the supplied ratio. Independent
conjunction cannot improve it from one even under a granted direct-sum bound;
for the actual parity seed there is an explicit linear-size circuit. Connected
parity constraints have satisfiability equal to the parity of all vertex
charges, regardless of expansion, by a spanning-tree construction.

The missing amplification operation remains unproved. The Murray-Williams
conditional bounds from the previous investigation give ratio at most epsilon/(c k^3),
so the quoted bounds do not meet the requirement; no impossibility of improving
those bounds is claimed. This is a derived proof specification and three tested
mathematical constructions, not a new lower-bound result, implemented algorithm,
or a P-versus-NP proof. No additional benchmark or Lean theorem was added.

## Previous continuation: attempt a general-computation proof (2026-11-10 JST)

The user explicitly returned the task to the complete P-versus-NP proof. We
examined two hierarchy/circuit routes without extending the stopped physical or
clause-learning benchmarks. Neither supplied a surviving complete-proof argument.
The deductions below audit attempted uses of known theorems; they are not claims
of new lower bounds or a new research result.

**Attempt 1: use P=NP to compress exponential computations, then contradict a
time hierarchy.** Let G be an explicitly encoded Boolean circuit that, given a
clause address j, outputs three variable addresses and their negation bits for
an exponentially long 3-CNF F_G. The encoding counts the circuit's input/output
wires, so all address lengths are polynomial in N=|G|. A witness circuit W maps
a variable address to its proposed Boolean value. Compose G with three copies
of W to form B(G,W), which outputs one exactly on the clauses that W falsifies.
Its size is polynomial in |G|+|W|, with no expansion of the full formula.
Thus the assertion that a particular small W is valid is

    for every clause address j, B(G,W)(j)=0.

Under P=NP this particular circuit-UNSAT check is polynomial-time. The step
that does NOT follow is the existence of polynomial-size W on every satisfiable
input G. To expose the gap, consider the separate premise:

    (EW) There is one polynomial p such that every satisfiable F_G has a
         satisfying-assignment circuit W with |W| <= p(|G|).

EW alone puts succinct 3-SAT in Sigma_2^P: existentially guess the polynomial
description of W and universally quantify the clause address. Succinct 3-SAT
is NEXP-complete; the locally accessible Cook-Levin reduction in Williams [W],
Theorem 3.1 and Corollary 3.1, together with polynomial padding gives the needed
small clause generators for any NEXP verifier. Consequently

    EW => NEXP is contained in Sigma_2^P.
    P=NP and EW => NEXP is contained in P.

The latter contradicts P != EXP from the deterministic time hierarchy, since
EXP is contained in NEXP. Equivalently, P=NP would force EW to fail. In fact,
under P=NP, for every k,C,N0 there would be a satisfiable succinct input G of
length N>=N0 with no assignment circuit of size <=C(N+1)^k. If all sufficiently
large satisfiable inputs had that bound, the finitely many smaller exceptions
could be absorbed into a larger constant, giving EW and the contradiction.
This conditional statement is not an unconditional witness lower bound.

The tempting invocation of an easy-witness theorem was invalid: [W], Lemma 3.1,
assumes NEXP is contained in P/poly, not P=NP. We read this restatement and proof
framework, not the separate original IKW paper. Indeed [W], Section 1.2, recalls
the known implication P=NP => EXP is NOT contained in P/poly. Neither a short
description of G nor a hypothetical polynomial SAT algorithm supplies EW.
Explicit self-reduction of F_G would still operate on its exponential length.
Repeatedly composing a transition circuit also lacks the required bound: the
[previous composition-cost audit](mcsp_state_reduction.md#why-repeated-squaring-is-not-a-free-shortcut)
already charges its growing circuit, rather than treating program reuse as
free evaluation. No replacement construction of W was obtained. Stop here.

**Attempt 2: upgrade algorithms-to-circuit-lower-bounds to P!=NP.** Murray and
Williams [MW], Theorem 1.1, gives, for a typical circuit class C and fixed
epsilon>0, the following implication: a nondeterministic O(2^((1-epsilon)n))
algorithm for Gap-C-UNSAT on n-input circuits of size 2^(epsilon n) yields a
constant c such that for every k,

    NTIME[n^(c k^4/epsilon)] is not contained in SIZE_C[n^k].

For unrestricted circuits this does not yet exhibit one language in NP outside
P/poly: the hard language may depend on k. The quantifier distinction is

    for every k, there exists L_k in NP outside SIZE[n^k],
    versus there exists L in NP such that for every k, L is outside SIZE[n^k].

Only the latter is a sufficient circuit route to P!=NP. This is a defect in
our attempted inference, not in the cited theorem. To check the distinction,
assume P=NP and let circuit UNSAT take time M^d on encoded inputs of length M.
For s=2^(epsilon n) gates, M=O(s(n+log s)). Choose
epsilon=1/(2(d+1)); then d*epsilon < 1-epsilon, including enough slack to
absorb the polynomial factors in n. The hypothesis of [MW], Theorem 1.1,
would hold, so its fixed-degree lower-bound conclusions also hold under that
P=NP assumption. They therefore cannot supply the desired contradiction by
themselves. P/poly permits the polynomial exponent to depend on the language.
Similarly, mapping each L_k to SAT introduces a reduction-size exponent that
can depend on k; we obtained no uniform bound that removes this dependence.

[MW], Lemmas 1.2 and 4.1, also require a fixed circuit-size bound on the whole
relevant nondeterministic class. P=NP merely supplies a potentially different
polynomial for each language. Substituting it for that stronger hypothesis is
not justified. Williams [W], Theorem 1.1, instead reaches NEXP outside P/poly;
that larger-class conclusion alone does not separate P from NP either.

**Decision and evidence.** No new candidate passes the repository's
[complete-proof criterion](solution_criteria.md#reporting-a-possible-resolution).
The missing compact-witness construction and the quantifier exchange are not
accepted as interface lemmas. No new solver, finite benchmark or Lean theorem
was added to make these failed bridges appear to advance the complete proof.
Code and mathematical result files are unchanged. The previous executable
commit `ec26f1c` passed its GitHub Python and both Lean workflows; that validates
the previous scoped results, not the present paper argument or P versus NP.

Primary papers read for this attempt:

- [W] R. Ryan Williams, *Improving exhaustive search implies superpolynomial
  lower bounds*, SIAM Journal on Computing 42(3), 1218-1244 (2013),
  [author PDF](https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf).
  Theorem 1.1; Section 1.2; Lemma 3.1; Theorem 3.1 and Corollary 3.1.
- [MW] Cody D. Murray and R. Ryan Williams, *Circuit Lower Bounds for
  Nondeterministic Quasi-Polytime: An Easy Witness Lemma for NP and NQP*,
  STOC 2018, [author PDF](https://people.csail.mit.edu/rrw/easy-witness-nqp.pdf).
  Lemmas 1.2 and 4.1; Theorem 1.1 and its proof in Section 5.

## Previous continuation: retain checked conflict information (2026-11-10 JST)

Pre-execution protocol for the user's requested repair: implement a small
deterministic search with unit propagation, resolution-based conflict analysis,
and optional reuse of the derived clauses. Both modes use the same first-variable,
false-first decisions and conflict-directed backtracking. The only search switch
is whether proved conflict clauses are available to later unit propagation.
Retain the proof log in both modes and count its size separately from the active
learned database. This is a controlled reference experiment, not a competitive
CDCL solver or a new clause-learning method.

The panel is fixed before execution: connected physical traps with 1, 4 and 16
blocks under two signed renamings; odd graph-XOR CNFs at 12, 24, 36 and 48
variables with two seeds; random density-six 3-CNFs at the same sizes/seeds;
and standard pigeonhole contradictions with 2 through 5 holes, using explicit
3-CNF clause splitting. Only the raw CNFs reach the search. Use at most 200,000
charged work units, 50,000 stored proof literals, 10,000 proof nodes, 10,000
active learned literals and decision depth 128 per run. Exhaustion is UNKNOWN;
do not increase a cap or drop a case after seeing results. Every SAT witness
must satisfy the original CNF and every UNSAT proof must replay independently.
Also replay all learned-clause derivations in SAT and interrupted traces.

Accept the narrow repair only if the physical cases are correctly solved under
these caps. Compare both search cost and stored information on the whole panel;
do not select a winner by counting only completed cases. Abort on an invalid
witness, proof or learned clause. The claimed general-polynomial bridge is
already excluded for this ordinary-resolution proof mechanism by the known
expander-Tseitin lower bounds cited in [robust_ceiling.md](robust_ceiling.md).
The finite run checks what this repair actually accomplishes; it does not
re-prove those bounds or establish the sampled graphs' asymptotic expansion.
Existing [CDCL experiments](cdcl_audit.md) remain the practical comparison.

**Execution outcome.** The protocol was committed as `bb41803` before running
the panel; its constants were unchanged. The
[reference implementation](../src/pnp_lab/retained_learning.py),
[paired experiment](../experiments/retained_learning.py) and
[saved report](../results/retained_learning.json) record all 26 inputs and
52 searches. Both modes returned 6 SAT, 10 UNSAT and 10 UNKNOWN. The same
10 inputs were interrupted in both modes; none was silently retried. All
physical cases were solved, including three for which the old bounded physical
restart baseline returned UNKNOWN. Both logical modes succeeded there, so
retention alone is not the cause of their recovery.

Among the 16 pairs completed in both modes, retention used fewer charged work
units in 3, more in 11, and the same in 2. The largest retained database in
this panel contained 1,683 literal slots. This observation neither proves an
asymptotic memory bound nor ranks practical CDCL solvers: the reference engine
rescans clauses and has no watched literals, deletion or restart heuristics.
All interrupted cases remain in the report. Their valid proof prefixes were
replayed too, without treating UNKNOWN as UNSAT. The eight parity controls were
also recognized from their raw CNFs and refuted by the existing Gaussian
algorithm, with independently checked row-sum contradictions.

**Narrow all-size explanation, derived after examining the traces.** The module
docstring proves that the abstract uncapped algorithm handles the connected
physical family in `b` decisions and at most `b` conflicts under arbitrary signed
renamings and clause reordering. Equality propagation fixes a whole touched
block. A wrong block value contradicts its positive triple and yields a unit
consequence; the correct value never needs to be undone. The resulting work is
polynomial on this family, even without retained clauses. The sampled runs
check the counts; the all-size statement relies on the argument, not extrapolation.
This replaces the obstructed physical trajectory with logical processing.

**Decision:** the specific counterexample is repairable. The proposal to obtain
a general polynomial SAT algorithm merely by preserving ordinary-resolution
conflicts remains stopped, for the existing known proof-system reason above.
Counting saved clauses is not a polynomial progress measure: there can be
`3^n` non-tautological clauses, and retaining an entailed clause does not remove
any genuine satisfying assignment. No new general inference mechanism, lower
bound for every SAT algorithm, or P versus NP proof has been obtained. Existing
literature limits are referenced here rather than presented as a new research note.

Validation: 504 unit tests passed, including all 256 proper two-variable CNFs
in both retention modes, independent small truth tables, proof corruptions,
explicit budget failures, and the signed physical controls. All 76 deterministic
reports, including the refreshed summary, match saved outputs; the previous
mathematical report fields are unchanged. The source hashes of the 55 files in
the earlier phase-20 Lean audit still match. This continuation adds Python
checks and a paper argument, not new Lean theorems.

## Previous continuation: test the physical restart bridge (2026-11-10 JST)

The user requested executing the bridge investigation and saving the accumulated
work, including the physical model, to Git. The
[new executable argument](../experiments/physical_restart_bridge.py) tests the
previous uniform-initialization repair on two explicit families. These are
elementary counterexamples to this search rule, with no claim of novelty.

For disjoint three-variable blocks, six equality clauses and one positive
triple give block energies `(1,2,2,0)` at Hamming weights zero through three.
Exact absorption probabilities are `(0,2/5,3/5,1)`. A product harmonic function
proves that `b` independent blocks have uniform-start success exactly `2^-b`
when run to absorption, and no greater success under a finite cutoff. A
separate full-kernel rational solver checks every state for one and two blocks.

The stronger obstruction is connected: use four-variable equality blocks,
one positive triple per block, and positive binary connectors between each
block's fourth variable and the next. The resulting formula has `4b` variables,
`14b-1` distinct clauses of width two or three, no units, and maximum occurrence
eight. Its unique solution is all ones. A zero block cannot change under any
one-bit nonincreasing-energy dynamics: the first three flips increase energy
by two, while the fourth increases it by at least one, regardless of neighboring
states. Uniform initialization avoids all zero blocks with probability
`(15/16)^b`. Thus success in at most `K` fresh global attempts is bounded by
`min(1,K(15/16)^b)`, even with adaptive coordinate selection or attempt duration.
With an input encoding of `O(b log b)` bits, no polynomial total-work budget
can maintain constant success probability on this family. At `b=1024`, even
`K=4096^3` attempts have success probability at most about `1.366680e-18`.
This is an evaluated consequence of the proof, not a simulated large instance.

The [fixed report](../results/physical_restart_bridge.json) contains finite
exhaustive checks of 4,368 connected assignments and 3,204 frozen-block flips,
two exact disconnected kernels, and 24 bounded runs of the actual restart
implementation. All returned witnesses are checked. Budget failures remain
UNKNOWN. The probabilistic theorems use ideal independent bits; seeded traces
do not establish those theorems. Independent tests also demonstrate that positive
temperature and collective moves can escape the zero-block condition, keeping
the scope of the obstruction explicit. No new Lean formalization was attempted.

Integration validation: 494 Python tests passed and all 75 deterministic
reports, including the summary, matched their saved outputs. Existing
mathematical report fields were unchanged. All 55 source hashes in the prior
complete phase-20 Lean audit still match; this integrity check is not a new
Lean build. Upstream's affine-lift, OBDD-order and resolution-miter work is
retained alongside the previously uncommitted formal and physical research.

**Decision:** stop the claim that uniform global restarts repair the existing
zero-temperature local solver into a polynomial general SAT solver. Component
decomposition alone does not repair the connected example. The formulas are
easy for other algorithms, so this supplies no lower bound for all SAT solvers
and no evidence assigning a probability to P=NP or P≠NP.

**Exact conditional bridge:** a uniform randomized algorithm with polynomial
worst-case bit cost, only checked witnesses, and success at least 2/3 on every
satisfiable input would put SAT in RP. NP-completeness and RP being contained in
NP then give NP=RP. This does not by itself yield P=NP. If one can additionally
construct, in polynomial time from each input, a polynomial list of polynomial
length random tapes guaranteed to include a successful tape whenever that input
is satisfiable, enumerating and checking that list decides SAT deterministically
in polynomial time. That stronger condition would yield P=NP. Neither condition
has been obtained here. A further physical proposal must change the obstructed
dynamics and prove the global resource and success bounds; naming equilibrium,
restarts, or a derandomization lemma does not supply them.

## Previous continuation: physical time evolution (2026-11-09 JST)

The user requested implementing a physical approach. The
[spin-energy model](../src/pnp_lab/physical_sat.py) maps arbitrary width-at-most-three
CNF to degree-at-most-three spin interactions, with energy zero exactly at its
models. It implements bounded classical lazy Metropolis trajectories with exact
rational acceptance, plus uniform initialization and zero-temperature restarts.
All returned witnesses are checked; exhausting time, precision or randomness
budgets returns UNKNOWN. Preparation and local-minimum detection are charged.

An easy unit-forced CNF family has energy `n-k+2k(n-k)` at weight `k`, and
`2n^2-n` clause positions. Exact birth-death recurrences show strong ground-state
equilibrium concentration together with extremely slow arrival from all zeros.
The module also proves an all-size deadline bound for every fixed temperature:
for even `n>=2`, success by tick `t` is at most
`min(1,(t+1)*max(2^(2-n/2),(127/128)^n))`. The cold case uses reversibility and
a middle-weight crossing; the warm case uses domination by independent bit
resets. This probability bound avoids the invalid inference from a large mean
alone to failure within polynomial time. The argument is not Lean-formalized.

The same family is easy from its explicit unit clauses. Uniform zero-temperature
restarts succeed with probability 1/2 per endpoint run and expected polynomial
total work. The revised implementation returned checked witnesses in all 12
bounded control runs. Thus the fixed-temperature, all-zero-initialized local
solver branch is stopped, while random initialization is an effective repair
for this family only. No general guarantee for the revised solver or UNSAT
decision has been obtained. Time-varying temperatures, collective updates,
quantum dynamics and all other physical methods are not excluded.
The [report](../results/physical_sat.json) and [figure](../results/physical_sat.png)
distinguish exact analysis, finite controls and evaluated all-size inequalities;
none is a measurement of hardware seconds or new evidence for P versus NP.

## Previous continuation: OpenAI ETH construction revisited (2026-11-09 JST)

The user's [DataCamp article](https://www.datacamp.com/blog/ai-exponential-time-hypothesis)
led back to the pinned OpenAI primary source, already covered by the
[reuse audit](openai_math_reuse.md). The new
[polynomial-repair experiment](../experiments/eth_polynomial_repair.py)
optimizes over all rational polynomials of the stated small degree in the
auxiliary swap construction. Across 51 parameter cases, one nonconsecutive
quadratic improves the correction rank by about 3.4% against the best
consecutive interpolation or constant choice. Its remaining defect exceeds
37% of the ambient dimension: this is not a complete small-tail SAT design,
an end-to-end speedup, or a novelty claim.

The analysis also rules out polynomial time by retuning the overview's
explicit coordinate/Taylor scans alone. Retaining its incidence-balancing
hypotheses separately forces a group of size at least sqrt(2n), even if
the spectral rank is calculated implicitly. These are bounds on named
constructions and sufficient hypotheses, not on all designs or SAT algorithms.
A complete-proof attempt needs a new balancing/evaluation mechanism that
handles the actual formula-dependent measurements. Counting their spectral
multiplicities does not provide that mechanism. No new complete-proof
candidate or upstream Lean replay is claimed.

## Previous continuation: two algebraic SAT mechanisms checked (2026-11-09 JST)

The [moment audit](../results/violation_moments.json) rejects deciding from a
short prefix of aggregate violation-count moments: opposite-status proper
3-CNFs agree through an order linear in the number of variables. These examples
are themselves Gaussian-solvable. This does not exclude computing more moments
efficiently or using other formula structure; no such general algorithm was found.

The [cubic-phase audit](../results/cubic_phase_sat.json) implements the standard
character-orthogonality reduction of SAT to a sparse cubic sign-sum zero test.
Its polynomial-time quadratic elimination control is correct; extending that
step unchanged to cubic phases fails even on the reduction of a one-gate AND
circuit, falsely returning zero. The required fast cubic zero test remains
absent. The executable modules contain the standard arguments,
budgeted reference evaluations and independent checks. No new mathematical-result
note, general SAT algorithm, all-algorithm lower bound or Lean proof is added.
This is a failed-shortcut check and a verified reduction, not a complete-proof
mechanism or evidence assigning a probability to P versus NP.

## Objective: return to P versus NP itself (2026-11-08 JST)

The user redirected the work to P versus NP after completion of the
[phase-20 F2 theorem](phase20_formalization.md). Preserve that checked theorem
as a completed proof-system result. Further refinements of its constants,
restricted-model formalizations and larger solver benchmarks are not the
current main task.

The return-to-goal audit found no established simulation taking an arbitrary
polynomial-time SAT decider to polynomial-size original-variable affine-clause
refutations. Circuit encodings describe computations, but the existing results
do not eliminate their auxiliary variables with the resource bounds needed
by phase 20. Nor does a refutation-length bound alone force a decider to output
such a refutation. Thus the completed theorem does not presently supply the
missing all-algorithm argument.

Use the existing [solution criteria](solution_criteria.md) as the admission
gate for subsequent candidates: a uniform, correct, polynomial-time algorithm
on all general 3-SAT inputs, or a lower-bound argument quantified over all
correct deterministic deciders and every polynomial time bound. Circuit-size
existence is not a uniform construction; a finite trend is not either result.
Candidate mechanisms must charge their actual bit costs, auxiliary variables,
shared subcomputations, preprocessing and witness discovery. Reject a candidate
when its essential lemma fails, without expanding its implementation merely to
accumulate more restricted results.

The matrix, shared-DAG rewrite and attempted MCSP streaming arguments remain
stopped for the reasons already recorded. No new surviving core argument or
P-versus-NP conclusion was obtained by this redirection audit. Choosing a target
equivalent to the goal is not itself a proof mechanism. The entries below are
historical work, rather than a claim that the experimental track remains active.

## Previous continuation: practical CDCL and independent proofs (2026-11-07 JST)

The [CDCL continuation](cdcl_audit.md) runs pinned Glucose 4.2.1 and
CaDiCaL 1.9.5 via PySAT on all 416 previous formulas and 288 larger fresh
formulas. Both solve every paired case, including all 22 previous DPLL
budget interruptions. Across 1,408 measured runs there are 267 checked SAT
models, 980 independently DRAT-checked refutations and 161 UNKNOWNs.
Another 516 truth-table/parity controls and rejection of a false proof
test the integration. All 224 graph-XOR inputs are also solved by the
polynomial Gaussian route, with checked original-row contradictions.

Larger random and XOR cases exhaust the requested conflict budget. Native
budgets are soft: one backend can overshoot by a large amount, so completed
fractions cannot rank speed at equal work. The report computes median
intervals under variable right censoring; every extended series has an
unresolved median, so the predefined complete-series curve comparison is
withheld. No completed-only fit, exponential-rate assertion or P-vs-NP
probability is reported.

The result strengthens the operational control: even multiple practical
CDCL solvers can struggle on a polynomial-time fragment. This does not
isolate clause learning causally, since branching, propagation and
preprocessing differ too. More finite solvers alone will not close the
all-algorithm quantifier. No active complete-proof mechanism or new
general lower bound follows. External runs/proof checking are optional,
separate from the standard-library core reproduction, with pinned source
and dependency manifests and saved native-binary provenance.

## Initial strategy: calibrated finite-size trends (2026-11-07 JST)

The [new experiment](sat_scaling.md) follows a [fixed protocol](sat_scaling_protocol.md)
comparing two auditable DPLL algorithms on random proper 3-CNF at two
densities and on a polynomial-time XOR control. Smaller sizes train
polynomial, square-root-exponential and exponential curves; larger sizes
compare their predictions. Work caps are retained as right-censored
observations, and non-exact medians are never fitted. Returned witnesses
and refutations are checked separately on original inputs.

Across 416 formulas, 810 of 832 DPLL runs completed and 22 were censored.
At density 4.25 the shortest-clause heuristic favored the exponential
model on held-out sizes; at density 6 the primary fits favored the
intermediate model, with changes under the predefined training-window
sensitivity check. These are finite distribution-specific observations,
not asymptotic rates or evidence quantifying the probability of P≠NP.

The polynomial-time control also favored exponential DPLL growth. Its
128 contradictions were all solved by reconstructing XOR rows from the
original CNF and checking Gaussian row-sum certificates. Thus the chosen
curve classifier cannot distinguish polynomial-time solvable fragments.
This supplies a concrete calibration against the invalid inference from
one solver's growth to all-algorithm hardness. No new complete-proof
candidate, general SAT upper/lower bound, or Lean extension is claimed.

Use measured failures to identify missing inference capabilities and
candidate mechanisms. Clause learning/restarts and external competitive
solvers were not tested here. Increasing the finite portfolio alone will
not establish a universal lower bound. Previous failed matrix and MCSP
branches remain parked.

## Previous strategy: Boolean matrix evaluation (2026-11-06 JST)

The user requested a new strategy. The [matrix evaluation attempt](boolean_matrix_sat.md)
switches to the P=NP direction: preserve Boolean laws with commuting
idempotent matrices and decide SAT by an ordinary matrix zero test.
It does not reopen the parked MCSP branch.

Standard orthogonal-idempotent decomposition classifies the method: a
d-dimensional tuple represents at most d assignments. Completeness for
all formulas with a tuple independent of the formula therefore forces
d>=2^n, already using singleton CNFs. Both one satisfying assignment and
the entire represented support can be recovered in polynomial time from
the matrices. This removes any hidden assumption about efficient
simultaneous diagonalization and shows that evaluation is equivalent
to checking an explicitly recoverable list of at most d words.

Formula-dependent complete polynomial-size tuples would suffice, but
a uniform polynomial-time constructor for them is equivalent to P=NP;
their dimension-one existence follows from having a satisfying assignment
and is not an algorithm for finding one. No such constructor was found.
The universal construction is rejected. The bounded matrix audit and
extractors were executed; no general SAT solver or Lean extension was
added. There is still no active complete-proof candidate.

## State-reduction outcome (2026-11-06 UTC)

There is no active complete-proof candidate. The current MCSP lower-bound
attempts are parked after the [state-reduction audit](mcsp_state_reduction.md).
This does not rule out hardness magnification as a field of research.

The attempted extraction of a hard answer from a streaming state must
charge the exponentially many reads needed to reach it. Exact iteration
of a Boolean transition circuit for a binary-encoded duration is
PSPACE-complete; a generic polynomial-time shortcut would imply P=PSPACE.
A conditional wrapper can also add an irrelevant PSPACE-answer component
to any putative fast MCSP solver while preserving its polynomial resource
bounds. The encoding uses truth tables H followed by zeros, all with an
explicit circuit below the n^2 budget. Hard state contents alone do not
force a hard update or a hard MCSP answer.

The note gives the complete configuration-simulation and gate-count
arguments and checks the easy-input circuit construction on 30 headers.
No new unconditional time lower bound follows. A new approach must supply
an actual resource-valid proof mechanism; further representation counter-
examples by themselves will not close the complete-proof objective.

## Starting audit for this cycle

The GitHub main reference was
[`6e34ce5`](https://github.com/HeliCorgi/p-vs-np-lab/commit/6e34ce5b3e98bc12c72c3916ea6bca0aa1a8cb05).
We inspected all 38 commit subjects on its main ancestry, the README and
research decisions, representative formal proofs, implementations, reports,
and failure records. All 409 base file blobs matched the GitHub tree before
editing. This is a scope-and-provenance audit, not an independent proof of
every assertion previously committed.

| Research phase | What remains useful | What stopped the argument |
|---|---|---|
| 1–4: boundary compression, XOR, and counting | Exact composition under explicit hypotheses; a reduction reaching general 3-SAT; witnesses and finite checks. [First claim ledger](research_notes.md) | Some chosen boundary representations need exponential size; quotient enumeration still has an exponential parameter. A correct decomposition on examples is not a uniform bound. |
| 5–10: small blocks, sparse choices, affine holes | Tractable fragments, explicit reductions and obstruction families. [Decisions and older baselines](reverse_engineering.md) | Sparse representation still encodes general SAT. A small local table or shorter certificate does not bound total discovery or composition. |
| 11–13: pruning and model transport | Precise target for reducing branch counts; transport and recovery on specified encodings. [Resolution barrier](layered_resolution_barrier.md) | Specific labels or resolution-justified substitutions require too many distinct states or large proofs. These are not lower bounds on arbitrary algorithms. |
| 14–15: modular and integer structure | Original-input certificates for hidden flow and prime-power obstructions. [Integer limits](global_integer_theory.md) | Even all raw affine laws on the allowed scopes can be trivial; singleton tests need not help. The [old recovery](modular_padding.md) depends on private pivots or other recognizable structure. |
| 16: preserve nonlinear relations | Exact finite thresholds on the 31-variable core, checked traces, and a proper-linear-3-CNF family hard for polynomial calculus over every field. [Proof boundaries](correlation_proof_boundary.md) | Bounded resolution width or PC degree is not complete; the preceding all-field lower bound did not by itself cover a system using additional integer lemmas. |

The starting [CI run](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/41819485348)
passed 341 tests, reproduction of 48 deterministic reports including the
summary, and 70 Lean theorem dependency audits. The independent 180-minute
[`openai/math` upstream attempt](../results/upstream_math_audit.json)
recorded a failed job without a verified terminal theorem/axiom result.
This is neither rejection of the upstream theorem nor a successful local
rebuild. Even the stated subexponential bound would not supply a polynomial
one. We retained the pinned sources and their integrity checks, without
restarting the expensive unfinished audit.

## Direct attempt at the missing core (2026-11-06 UTC)

The user asked to address the missing streaming lower bound itself. The
[direct attempt](mcsp_update_core.md) tests actual proposed arguments:
prescribed-witness hardness, unavoidable updates, and a minimum-circuit
potential. A coNP-complete validation predicate can coexist with a trivial
repair on the very same reachable zero prefixes. A known candidate can
also be checked during the long input stream with polynomial work per bit.
Neither observation proves that every algorithm incurs a slow update.

For prefix p=00101 on three inputs, two explicit three-gate circuits
give opposite next bits, while no circuit of two gates fits p. Thus
mu(p)=mu(p0)=mu(p1)=3: a forced representative change need not increase
minimum size. A point-indicator construction also proves
mu(p) <= mu(pb) <= mu(p)+2n+3. An unavoidable first rejection therefore
has its previous minimum size in (s-2n-3,s], but recognizing that boundary
efficiently or proving it hard remains unresolved.

These are elementary paper arguments with a bounded reproducible audit,
not a new MCSP solver or a Lean extension. The audit checks the small
counterexample exhaustively, 2,120 point repairs and 16 validation/search
controls. None supplies the all-algorithm, all-polynomial lower bound.
There is still no complete proof or surviving proved core mechanism.

## Early-pruning continuation (2026-11-06 UTC)

The user explicitly permits stopping unpromising branches early. Apply
this before building another solver or formalizing a restricted result:
state the exact implication to P=NP or P≠NP, its unresolved hypothesis,
and what the proposed argument does beyond the already rejected approach.
If the route fails that check, record the reason and stop it. A conditional
bridge or a finite experiment is not itself a complete-proof candidate.

The [MCSP streaming audit](mcsp_streaming_gate.md) checks a genuine route
to P≠NP against McKay–Murray–Williams, STOC 2019, Theorem 1.3. It fixes
ordinary circuits of size s(n)=n^2, lexicographic truth-table order, uniform
one-pass search algorithms, and polynomial-in-s space **and** update and
reporting time. The needed lower bound quantifies over every algorithm
and every fixed polynomial. A self-contained prefix-repair argument
reconstructs the P=NP implication underlying this known bridge.

The memory-only attack fails immediately: even without P=NP, exhaustive
repair maintains one prefix-consistent circuit in O(s log s+n) space.
Only its update time is large. Ordinary polynomial identity testing also
does not test Boolean-cube identities, and magnification with an endpoint
such as NP not contained in NC1 alone does not give P≠NP. These branches
were cut before adding experiments. A direct diagonal simulation did not
respect the same size-s budget for arbitrary polynomial update exponents.

No new all-algorithm lower bound or active proof candidate resulted. Stop
phase-28 implementation work. Retain the sourced target as an open
obligation; do not assume that all future streaming algorithms must use
the particular repair routine. No new executable, formal theorem or test
count is claimed in this continuation.

## Phase 28: execute a shared-circuit SAT alternative (2026-11-06 UTC)

The user requested a different method. The new [shared-DAG solver and
audit](shared_dag_sat.md) pursue the P=NP direction without expanding
nonlinear definitions into polynomials. The exact cofactoring procedure
uses structural hashing, constants, XOR cancellation, whole-sum common
factors and memoized decision results. It accepts circuits or CNF, checks
SAT witnesses on the input, and distinguishes UNKNOWN on resource exhaustion.

The proposed polynomial state bound is false: a linear-size circuit family
requires at least 2^(k-2) nonterminal states with the stated a-first order.
The paper proof counts actual UNSAT search states, not a full representation
that a decision procedure need not construct. The same circuits need at
most two states with selectors first, and a one-selector factoring control
needs none. No all-order or all-algorithm hardness follows. The precise
family is independently zero by Boolean algebra and by finite polynomial
expansion; small truth tables and ten new tests check the implementation.

Keep the executable and counterexample as regression artifacts. Reject the
all-input sharing/local-rewrite hypothesis; further tuning this variable
order does not answer the missing uniform complexity bound. General
semantic circuit equivalence cannot be assumed as a free compression rule.
This is a Python implementation and paper argument, with no additional Lean
claim, no novel-algorithm priority claim, and no complete P-versus-NP proof.

## Phase 27: degree-accounted extensions and the sharp limit (2026-11-06 JST)

The [extension substitution theorem](extension_substitution.md) is now part
of the ordinary-PC Lean package. A degree-B extended proof substitutes to
an ordinary proof through degree DB when every coordinate polynomial has
degree at most D, original Boolean axioms are present, and definitions hold
on the entire original Boolean cube. The new gate lemmas discharge that
semantic premise for the stated AND/XOR/NOT coordinate choices. The package
build and all 142 transitive axiom audits passed, including 16 new endpoints.

The formal obstruction is also explicit: AND of n variables has polynomial
degree at least n under every representation of its Boolean function, even
though it has n-1 binary gates. Substitution of the output Boolean axiom
then produces an ordinary degree-2n polynomial. This makes the direct
line-by-line transfer factor sharp; it is not a lower bound on all possible
refutations or simulations. OR supplies a separate exponential sparse-size
control, while XOR and the previous inner product have low coordinate degree.

Five new independent tests and a deterministic report check the executable
coordinate expansion, ordinary Boolean corrections, and explicit resource
limits. Stop trying to infer bounded coordinate degree or polynomial sparse
expansion from polynomial gate count. The theorem remains useful for its
bounded-degree class. A general argument preserving auxiliary definitions
and shared circuit/proof size is still missing; no complete P-versus-NP proof
or candidate meeting the full goal has been obtained.

## Phase 26: nonlinear extensions and the goal-level gate (2026-11-06 JST)

Starting checkout was `68646aaf6af142a354d04c33c412e012900b9ebd`, including
phase 25's exact `2^m-1` cover number. The user reaffirmed a complete proof
of P=NP or P≠NP as the objective. We stopped further affine-cover sharpening
as the primary route: it does not address general computation.

The [new extension audit](circuit_extensions.md) implements unique-extension
Tseitin CNF and an explicit ordinary-resolution proof generator for duplicate
circuits with opposite outputs. For the inner-product family, the paper proof
gives width three and exactly `32m-18` proof lines. Seven new independent
tests and a deterministic report include replay through `m=1024`, as well as
SAT controls and proof tampering. This tests the precise proposed simulation
boundary; it neither refutes the earlier expander lower bound nor provides
a general circuit-equivalence or SAT algorithm.

The note also proves that uniform polynomial-time existential projection of
arbitrary Boolean circuits is equivalent to P=NP. Retaining nonlinear gates
avoids the chosen affine representation obstruction but leaves this global
computational problem unresolved. No complete P-versus-NP proof or candidate
meeting its quantifiers was obtained. The old expander and full restricted
lower-bound formalizations remain separate work; do not claim them finished.

## Phase 24: the affine-cover/circuit boundary (2026-11-06 JST)

The actual unfinished continuation was `research/affine-cover-circuit-boundary`
at `54f7d62a74f4943007b39c39b2197e186ddae44e`, ahead of main `9dd8e876`.
Its quadratic polar module failed to compile. Repairing its sum binder scope,
explicit functional extensionality, and constant second-difference cancellation
completed the intended dimension theorem without weakening its statement.

The [connected counting proof](affine_cover_circuit_boundary.md) now derives
an exponential affine one-cover bound for the binary inner-product function:
on `2m` original input bits, at least `2^(m-2)` charts are required for `m >= 2`,
even with overlapping images. The dimension bound and a sufficiently large
positive subset are proved internally. A linear-size circuit for the same
function refutes the precise proposed translation from arbitrary small
circuits to small exact affine covers on their original inputs. The circuit
gate count is a paper construction, separate from the named Lean endpoints.

The complete package build and 126 endpoint axiom audits, including 20 new
endpoints, passed at `6aa1b3fe` in
[run 42125609896](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42125609896).
The [audit record](../results/affine_cover_formal_audit.json) retains source
hashes, actual axiom sets, the three failed checkpoints, and the separate
successful core/reproduction workflow. All 388 tests and 62 deterministic
reports passed there. The local unit suite also passed all 388 tests once its
required fixtures and CLI files were present. No package pin, foundation
source, workflow permission, or proof-system premise was changed.

This is an elementary representation obstruction, with no priority claim.
It neither resolves P versus NP nor excludes every possible simulation into
an affine-clause proof system. The earlier expander separator, quantitative
existence/counting, full exponential formalization, and intrinsic distinct-flat
deduplication remain unfinished. A P-versus-NP-relevant next target needs an
explicit efficient simulation and a bound valid for the model it uses; the
rejected same-input affine-cover translation cannot supply that bridge.

## Phase 23: optimal affine parameters (2026-11-06 JST)

The user selected the exact unfinished chart theorem. Starting main was
`6ffad1cdb12c0d8a78324581010584313afb1eaa`; all 517 file blobs matched, both
main workflows were successful, no open PRs were present, and the latest
commits and current proof/decision records were inspected. The task stayed
within that target and its direct restriction/DAG consequences.

Four [new modules](optimal_affine_parameters.md) recover affine coefficients
in the ordinary polynomial ring, prove consistency preserves slope rank,
derive common-kernel dimension over an arbitrary field, and construct the
exact affine map with `n-spanRank C` parameters. Its coordinate-polynomial
encoding has degree at most one, exact image, and injectivity. The intrinsic
restriction budget and source-DAG criterion now construct their charts;
empty zero-sets have no index in the sum. Repeated node occurrences are still
counted separately. All original source and actual-PC separation premises
remain explicit.

The complete hosted build and 106 named endpoint audits passed at `e8bf0ee`
in [run 42116967349](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/42116967349).
The [audit record](../results/optimal_affine_formal_audit.json) retains exact
source hashes, observed axiom sets, and both earlier failed checkpoints.
Their repairs were an explicit nonzero degree-one exponent and a direct
basis choice from the already proved dimension formula. No theorem statement
was weakened and no axiom or proof hole was added. An independent internal
statement audit found no defect in exact image, dimension, empty-set handling,
or the connected criterion's retained premises.

Independent local reproduction passed 388 tests and matched 62 deterministic
reports with the current source hashes. No new finite benchmarks, vendored
sources, package pins, or workflow settings were added. Classical basis choice
is a mathematical construction, not a new executable elimination algorithm.
The expander separator, quantitative existence/counting, and full exponential
formalization remain unfinished. No P versus NP resolution was obtained.

## Phase 22: Boolean restriction dimension (2026-11-06 JST)

Starting main was `42e2dde0d32bd19a4fdce4b701d3b1f5525906a1`.
All 511 file blobs matched the local tree, recent history and open PRs (none)
were checked, and both main workflows had succeeded. The preceding proof
modules, explicit scope boundaries, and next acceptance test were read before
choosing this cycle's target.

The [new restriction proof](boolean_restriction_dimension.md) constructs
linear maps into actual Boolean function spaces, proves their kernel meaning,
and proves their image dimensions are at most the explicit truncated binomial
sum. A clause-level adapter connects raw initial polynomials and compressed
derived polynomials to the existing semantic DAG replay. The composed theorem
therefore proves its numerical image budgets internally. Supplied affine
parameterizations and coverage remain explicit data; optimal intrinsic
dimension is not assumed.

The four new modules compiled on their first hosted attempt. Thirty new theorem
endpoints extend the ordinary-PC axiom audit from 38 to 68; only standard
logical axioms were observed. The [new audit record](../results/boolean_restriction_formal_audit.json)
preserves exact sources and CI evidence. A focused independent internal
statement audit found no coverage-direction or hidden-conclusion defect and
confirmed that all tagged input clauses have the stated raw width bound.
No new upstream source files or finite benchmark reports were added.

The next target is a bijective affine parameterization of each nonempty clause
zero-set with exactly `n - spanRank C` parameters, followed by the expander
separator and quantitative proof. The full exponential bound remains a paper
proof with incomplete formalization and no external specialist review. No
P versus NP resolution or general polynomial-time SAT algorithm was obtained.

## Phase 21: ordinary-PC formalization cycle (2026-11-05 UTC)

Starting main was `08ab7b79d1537b444a42bbec4d374e24090aae70`.
All 491 file blobs matched the local snapshot; the current README, research
decisions, phase-20 proofs and failure controls, recent commits, open PRs
(none), and successful main CI were checked. The selected task was the exact
first gate left in phase 20: formalize the ordinary-PC replay, rather than
increase the finite benchmark sizes.

The [phase-21 package](ordinary_pc_formalization.md) contains actual ordinary
polynomials and primitive degree-bounded PC derivations, a complete weighted
semantic-DAG replay, concrete basis-compressed affine indicators, and a
connected dimension-budget theorem. Its hosted Lean build and transitive axiom
audit passed, with 38 named theorem audits allowing only standard logical
axioms. The [source/CI record](../results/ordinary_pc_formal_audit.json) preserves
the actual result separately from Python reproduction. The geometric restriction image
and expander separator remain explicit missing bridges to full formalization
of the exponential lower bound.

Three unmodified MIT-licensed foundation files by Kamil Braun are reused with
full attribution, pinned hashes, and license notices. Their first hosted build
succeeded. The initial lab modules exposed elaboration issues (a comment
delimiter, universe/decidability inference, explicit zero/one cases, and a
dimension rewrite). A later literal-injectivity timeout was resolved by typed
equalities without changing the theorem or raising heartbeat limits. These
failed checkpoints are followed by the successful complete package build and
axiom audit. No mathematical counterexample to the replay
argument was found in this bounded audit. Selective compilation does not
certify the upstream bit-PHP theorem. The old `openai/math` snapshot and its
failed 180-minute audit record are preserved without relaunching that build.

The [next acceptance test](reverse_engineering.md) is the actual Boolean
restriction map with its squarefree dimension, followed by the published
graph-reduction interface. The [general lower-bound register](strong_lower_bounds.md)
preserves the phase-20 paper theorem with its current evidence level. No
all-algorithm lower bound or polynomial-time general SAT algorithm has been
obtained.

## Phase 20: dated outcome (2026-11-05 UTC)

**Formalization completion, 2026-11-08 JST:** the actual normal forms,
ordinary-PC separation, connected-obstruction density, semantic distinct-flat
count and source-DAG budget are now composed with a proved support-family
existence theorem and the explicit exponential specialization. The final
`Phase20.exists_unsat_exponential_lower_bound` has no family-existence,
separation, density or asymptotic comparison premise. It quantifies over every
`n ≥ 16 * 1024 * 12288^4 * 10^16`, constructs an UNSAT proper linear 3-CNF
with `12n` clauses and occurrence at most 4096, and bounds both source-DAG nodes
and distinct nonempty high-rank false flats by
`(1/4) * exp(n / (81 * 2^65 * 10^32))` from below. The full package build and
390 theorem axiom audits (70 new endpoints after the earlier 320) passed locally.
See the [exact scope and proof map](phase20_formalization.md) and
[source-bound record](../results/phase20_complete_formal_audit.json).
This completes the specified F2 proof-system theorem. External review,
priority assessment and an all-algorithm lower bound remain separate questions.
The following paragraphs preserve the original paper-stage outcome.

Starting main was `c6a2b2e758c618c355149b70fc24437c470db145`.
Its 474 file blobs matched the local tree before editing. Recent history,
open PRs (none), and successful head CI runs were checked. This cycle took
the preceding separated-space question seriously rather than relabeling
the earlier PC refutation-degree bound.

The [direct common-annihilator theorem](affine_dag_annihilator.md) bounds
semantic unary/binary affine-clause DAGs by a low-degree separated-space
dimension. The [expander construction](expander_separated_space.md)
supplies such a space and a fixed occurrence bound, leading to an
exponential node-count bound, and even an exponential count of distinct
high-rank falsity flats, on an existential proper linear 3-CNF family.
Arbitrary sharing, depth, and parity support are allowed. The source lines
remain affine clauses on the original F2 variables. This paper argument
was examined within the original cycle; at that checkpoint, complete
formalization, external review, and priority assessment were outstanding.
The completion note above updates the formalization status.

The [upstream source audit](braun_generic_audit.md) read and hash-verified
17 additional pinned Lean files. No upstream build was run. The new
direct proof removes the registry/removal theorem from this lab result's
dependencies; the published Mikša–Nordström graph-reduction theorem remains
an explicit mathematical input.

Three new reproducible reports audit actual PC consequence spaces,
masked DAG-to-PC traces, and support/parameter counts. Failure controls
separate static from dynamic polynomial consequences and individual
nonmembership from independence of a span. The Lean addition verifies
six semantic and budget lemmas, not the complete lower-bound theorem.
This is a strong proof-system result recorded independently of the ultimate
goal. No polynomial-time general SAT algorithm, all-algorithm lower bound,
or P versus NP resolution has been obtained.

## Phase 19: dated outcome (2026-11-05 JST)

Starting main was `8bfca4c451d6be1cbc84be50f9d6f667f66528a3`.
All 455 file blobs matched its recursive Git tree before editing; recent
commits, open PRs (none), and completed CI runs were checked. The cycle
addressed parity queries, the specific next gate left in phase 18.

The [general expansion theorem](parity_localization.md) now covers short
parity questions with arbitrary-modulus integer terminals. A complementary
[same-field theorem](parity_pc_bridge.md) covers arbitrarily wide parity
queries with bounded-degree ordinary-PC terminals, including heterogeneous
degree budgets. Both are tree results, with all restrictions stated. The
[strong lower-bound record](strong_lower_bounds.md) retains these reusable
statements and attributes established results separately.

The new finite artifacts audit both-answer extension, a rank-charge
counterexample, original-clause parity certificates, and legal ordinary-PC
branch discharge and composition. The simple parity-block positive class
has a proof-discovery and bit-cost argument, not just a short supplied proof.
The [primary literature map](parity_query_prior_work.md) also records a
September/November 2026 unrestricted-DAG claim. Its
[bounded semantic source review](braun_resoplus_audit.md) does not certify
the entire external formalization, and it is not a premise of the lab's
new proofs. No all-input SAT algorithm, general algorithmic lower bound,
or P versus NP solution candidate was obtained.

## Phase 18: dated outcome (2026-11-05 JST)

The new [support theorem](support_localization.md) answers the previous
high-digit question negatively on the lab's existing all-field-hard
expander family. Even [trees of variable queries with integer refutation
leaves](conditional_localization.md) have an exponential leaf lower bound
there at fixed width and local scope. A separate [Boolean field-switch
family](field_split_boundary.md) admits polynomially discovered mixed-field
proofs with one split, yet its [unpinned integer relaxation](coprime_pseudomarginals.md)
survives every modulus. This is consistent with published two-prime CSP
constructions; it is not an all-input lower or upper bound. The new
[acceptance test](reverse_engineering.md) concerns rules genuinely outside
the variable-tree model such as wide parity queries or certified branch
sharing. The ongoing objective and standard for a solution remain unchanged.

## Phase 17: question, evidence, and stopping decision

**Falsifiable question.** Can independently justified nonlinear clauses
enable global arithmetic on a whole family where the raw integer stage
is blind, the previous private-variable rule cannot start, and ordinary
resolution alone is provably expensive? Exclude a mere increase in caps.
Require an original SAT word or replayable UNSAT proof, account for finding
it, and identify an input class on which this feedback still fails.

- **Paper proofs:** [signed implication shields and both-side family decision](feedback_separation.md);
  [composite carry recovery](feedback_carry.md); [degree simulation of one final integer sum](feedback_simulation.md).
- **Executable evidence:** [parity and failure controls](../results/integer_feedback.json),
  [prime powers](../results/feedback_prime_power.json), [first-digit coefficients](../results/feedback_simulation.json),
  [higher-digit identities](../results/feedback_digits.json). Finite identity checks are not the uniform degree proof.
- **Lean scope:** [binary edges, path composition, replacement in a disjunction, and sound transport of an integer refutation](../Formal/IntegerFeedback.lean).
  The quantitative separation, degree simulation and Python code are not formalized here.
- **Negative result:** the front end can recover the *entire* source formula
  on an NP-complete class yet produce no local integer information. Neither
  more examples of the same shields nor larger fixed local tables answers this.

**Next acceptance test.** On the prior all-field-hard family, small learned
clause width and small integer scopes would require a genuinely high
detecting digit in every successful one-sum proof. Seek a family and an
algorithm with independently justified hardness for the comparison system,
polynomially discoverable arithmetic certificates, and an accounted total
bit cost. Rule out trivial rescaling and low-width explanations. If that
route fails, publish the precise obstruction or switch to a different proof
language; do not silently assume the new language inherits old bounds.

Each future cycle starts from current main and unfinished work, states a
testable hypothesis, and stops on a verifiable advance or a documented
failure. An apparent all-input solution triggers independent adversarial
review and a **candidate** notice. Finite measurements, a restricted family
theorem, bounds for a chosen proof system, or a successful Lean build alone
do not trigger a solution announcement.
