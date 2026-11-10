# What would constitute a solution of P versus NP?

This note fixes the mathematical target before assessing a new algorithm. It
contains definitions, deductions from them, and a claim checklist. It does not
claim a solution, a new lower bound, or a new algorithmic result.

The reference definition is Stephen Cook's official Clay problem description,
Section 1 and the appendix. Its Definitions 3–4 and Proposition 1(c) give the
reduction criterion used below [C]. The document is historical; its dated
remarks about the fastest algorithms or contemporary hardware are not used as
current facts.

## 1. The object being decided

Fix a finite encoding alphabet, which may be binary. A decision problem is a
language `L ⊆ {0,1}*`. An input is a finite string `w`, and its size is its
**encoded bit length** `N = |w|`. A decider returns one bit and halts on every
input. Malformed strings must have a specified answer, such as rejection after
parsing.

For a deterministic Turing machine `M`, let `t_M(w)` be its number of steps,
with value infinity if it does not halt. Then

\[
L\in\mathrm P
\quad\Longleftrightarrow\quad
\exists M\;\exists k\in\mathbb N\;\exists C>0\;\forall w:
\left[M(w)=\mathbf1_L(w)\ \land\ t_M(w)\le C(|w|+1)^k\right].
\]

There is one finite machine description. The constants `C` and `k` may depend
on that machine, but not on the particular input or its length. This is an
equivalent convenient form of Cook's polynomial bound [C, pp. 1–2].

A language is in `NP` when there is a deterministic polynomial-time verifier
`V` and a polynomial `p` such that

\[
 w\in L\quad\Longleftrightarrow\quad
 \exists y\in\{0,1\}^*,\quad |y|\le p(|w|)\ \land\ V(w,y)=1.
\]

The verifier's running time is polynomial in the length of its explicitly
given inputs. This existential witness condition is Cook's checking-relation
definition [C, p. 2]. It does not supply a method to find `y` efficiently or to
recognize that no such `y` exists. We have `P ⊆ NP`: a polynomial-time decider
itself is a verifier that ignores the witness.

The question is whether these two sets of languages are equal. Polynomial time
is an asymptotic mathematical condition. A bound such as `N^100` qualifies;
`2^sqrt(N)` and `N^log(N)` do not, even if particular input sizes run quickly.

## 2. The sufficient algorithmic route: SAT or 3SAT in P

Let `SAT` be the language of encodings of satisfiable Boolean CNF formulas.
Let `3SAT` restrict each clause to at most three literals. Both are
NP-complete. Here “NP-complete” uses polynomial-time many-one reductions: for
every `L ∈ NP`, a function `f_L` is computed in polynomial time and satisfies

\[
 w\in L\quad\Longleftrightarrow\quad f_L(w)\in\mathrm{3SAT}.
\]

Cook states the completeness and reduction implication in Section 2 [C,
pp. 3–5]. The resulting argument is short. If a deterministic algorithm decides
3SAT on length-`s` inputs in `C(s+1)^k` steps, and the reduction takes at most
`q(N)` steps, then the reduction's output has polynomial length. Running the
reduction followed by that algorithm takes at most a polynomial such as

\[
q(N)+C\bigl(q(N)+1\bigr)^k.
\]

Thus every `L ∈ NP` lies in `P`, and `P = NP`. A polynomial-time algorithm for
unrestricted SAT gives the same conclusion. Equivalently,

\[
\mathrm P=\mathrm{NP}
\quad\Longleftrightarrow\quad
\mathrm{SAT}\in\mathrm P
\quad\Longleftrightarrow\quad
\mathrm{3SAT}\in\mathrm P.
\]

For our algorithmic route, a proof must therefore establish all of these:

| Obligation | Required statement |
|---|---|
| Coverage | Every valid SAT/3SAT instance is accepted as input, or is reduced to the proposed class with a polynomial-size, polynomial-time, satisfiability-preserving map. |
| Correctness | For every input, the output is SAT exactly when a satisfying assignment exists. |
| Totality | The procedure halts for SAT and UNSAT instances alike. |
| Worst-case cost | One fixed polynomial bounds its total bit-computation time on all encoded inputs. |
| Uniformity | One finite algorithm constructs everything it needs; no uncharged advice, oracle, or separate table for each input length is assumed. |

An explicit usable implementation is not a logically necessary condition for
a proof of `P = NP`. A valid nonconstructive proof that the required
polynomial-time decider exists would also suffice; Cook explicitly discusses
this possibility [C, p. 7]. We choose the algorithmic route because it gives
concrete semantics and cost obligations to investigate.

### The current mixed-constraint target

The repository now has an explicit coverage bridge even for **2-CNF plus
three-variable XOR**. Each 3SAT clause can be replaced by

\[
 a\lor b\lor c\quad\Longleftrightarrow\quad
 \exists u,v,w:\quad (a\lor u)\land(b\lor v)\land(c\lor w)
                  \land(u\oplus v\oplus w=0),
\]

using fresh helpers for each clause. The proof and polynomial construction are
in [the reduction note](two_cnf_xor_reduction.md) and
[the reverse-engineering note](reverse_engineering.md). Therefore a uniform
deterministic polynomial-time decider for this restricted mixed language
would already imply `P=NP`. The reduction preserves satisfiability and
projection to original models; its variable number of helper extensions means
it does not preserve model counts.

For a consistent XOR system, the
[implemented mixed solver](mixed_solver.md) distinguishes

\[
 d=n-\operatorname{rank}(A),\qquad
 r=\dim\operatorname{span}\{a_i:i\text{ occurs in the normalized CNF}\}\le d,
\]

where `x_i=c_i+⟨a_i,t⟩` parameterizes the affine solutions by `t∈F_2^d`.
Enumerating all free assignments is a `2^d poly(N)` reference method; the
implemented quotient search needs only `2^r poly(N)` bit time as an upper
bound. Its `effective_rank` is this observation rank, not a minimum semantic
measure of nonlinearity.

For the baseline all-cell search, a general polynomial bound is already ruled
out: exactly-one CNF on `k` variables together with even XOR parity has
`d=r=k-1`, is UNSAT, and forces exactly `2^(k-1)` cell visits in unbudgeted
**decision mode** as well as in exhaustive mode. The input has polynomial
encoded size `O(k^2 log k)`, so this is a superpolynomial worst-case lower bound
for this implementation. The [all-size argument](reverse_engineering.md) does
not lower-bound other SAT algorithms; the family's contradiction itself is
easy to recognize. Improving finite performance or formally proving this
same enumerator correct cannot remove its known worst-case enumeration.

The subsequent [certified parity-cut preprocessor](parity_cuts.md) does change
that algorithm: it refutes the exactly-one/even family without enumerating
cells. It still has superpolynomial worst cases, including exactly-two CNF
with odd parity and odd-cycle formulas passed through the 3SAT bridge. The
bridge CNF alone has full affine hull, so even a complete extractor of
unconditional affine consequences from that CNF cannot strengthen it. This is
a rigorously specified inference-method limitation, not a lower bound against
joint CNF+XOR reasoning or against every SAT algorithm.

The [stage 4 joint inference](joint_reasoning.md) does use both fragments and
removes that encoded odd-cycle obstruction, with checked certificates. The
exactly-two obstruction remains for the implemented rule set. The separate
[signature counter](signature_counting.md) handles group-local CNF joined by
cross-group XOR, but its table sizes and construction can still be exponential.
Neither development supplies the universal polynomial bound required above.

The [constant-block reduction](constant_block_bridge.md) makes the remaining
target more specific: general 3SAT is already expressible with group-local
2-CNF on groups of at most five variables, coupled by disjoint ternary XOR
rows. Polynomial local table construction alone is therefore insufficient.
A uniform polynomial algorithm for the whole resulting mixed instance would
meet the `P = NP` criterion; this reduction does not prove it impossible.

The [October 2026 ETH release and review](prior_work.md) also leave the target
unchanged. A uniform `2^{o(n)} poly(N)` SAT algorithm would refute ETH. This
form alone does not give a polynomial bound. To obtain one from such an
estimate, the exponent must be `O(log N)`, with all remaining factors and
preprocessing costs polynomial in `N`. Conversely, a displayed subexponential
upper bound is not a superpolynomial lower bound on the actual algorithm and
cannot prove `P != NP`.

## 3. SAT, UNSAT, and certificates

A SAT certificate is a satisfying assignment. Checking it answers the question
“does this particular assignment work?” It does not establish a polynomial
bound on the search that found it.

A complete decision algorithm must also correctly return UNSAT. It need not
emit a separate short UNSAT certificate in order to belong to `P`: a correct,
polynomial-time computation already meets the decision definition. However,
if the proposed procedure delegates UNSAT to a certificate generator, another
solver, or an oracle, that component's correctness, completeness, and time are
part of the algorithm being analyzed. A fast proof checker alone does not
bound the time or size of proof generation. A timeout means unknown, not
UNSAT.

Even proving that every UNSAT formula has a polynomial-size, polynomially
checkable certificate would establish `NP = coNP`, via SAT completeness.
That statement is not currently known to imply `P = NP`. The missing issue
for this algorithmic route remains uniform deterministic decision time,
including finding any certificates that the procedure needs.

Conversely, a polynomial-time SAT decider yields a polynomial-time search
procedure. First decide the formula. If it is satisfiable, fix variables one
at a time, asking whether setting the next variable to zero leaves a
satisfiable instance; choose one if not. There are at most a linear number of
decision calls in the number of explicitly occurring variables, each on a
polynomial-size formula. This is a direct construction, and it includes the
initial UNSAT test. A search routine that succeeds rapidly only on SAT
instances does not meet this decision requirement.

## 4. Cost is measured in input bits and includes construction

The definition makes several implementation distinctions unavoidable.

- **Encoding.** A number written in binary costs its bit length, not its
  numeric value. A loop with one iteration per possible value can be
  exponential in the encoding length. For SAT, count variable identifiers,
  literals, clauses, and any auxiliary constraints. Rename occurring
  variables or explicitly encode a variable table; a huge unused variable
  label must not silently create exponentially many variables.
- **Preprocessing.** Building an index, discovering a decomposition, finding a
  basis, constructing a circuit, compiling a boundary relation, and choosing
  an elimination order are computations. They are included in the total.
- **Intermediate sizes.** Count every retained row, clause, state, node, and
  its representation length. An exponential table is not a polynomial-size
  representation merely because a program stores a reference to it.
- **Bit operations.** A Python integer storing `2^n` bits needs that many
  bits. Treating XOR or multiplication on an arbitrarily long integer as
  one constant-time operation can hide the cost. Exact real or arbitrary
  precision arithmetic also requires an appropriate cost model and a
  polynomial simulation in the ordinary bit model.
- **Composition.** Polynomial time for one local operation does not give a
  polynomial total if the procedure performs exponentially many operations.
  A polynomial-depth binary search tree can have exponentially many nodes.
- **Uniformity.** A polynomial-size circuit for each input length, with no
  uniform construction, is a nonuniform resource. It is not by itself a
  polynomial-time Turing-machine algorithm. An external SAT oracle similarly
  changes the problem being solved.
- **Mode of guarantee.** An average-case, expected-time, randomized, quantum,
  or heuristic guarantee is not the deterministic worst-case guarantee in
  the displayed definition. Additional theorems would be needed to derive
  that guarantee from such a result.

These are deductions from the choice of machine and input-size model, not
additional empirical requirements. Polynomial time can be proved without
benchmarking, while benchmarking cannot replace the bound.

## 5. What the opposite direction would have to prove

Because SAT is NP-complete, `P ≠ NP` is equivalent to `SAT ∉ P`. In explicit
quantifier form, using the full encoded SAT language, this is

\[
\begin{split}
\forall A\text{ that correctly decides SAT}\;\forall k\in\mathbb N\;
\forall C>0\;\forall N_0\in\mathbb N\;\exists w:\qquad\\
|w|\ge N_0\quad\land\quad t_A(w)>C(|w|+1)^k.
\end{split}
\]

Each `A` here is a deterministic total decider. The hard input can depend on
`A`, `k`, `C`, and `N_0`. The arbitrary-size form follows because finitely many
exceptional small inputs can be absorbed into a larger constant. It does not
claim that every input is hard or that one particular input is hard for all
algorithms.

This needs **superpolynomial**, not necessarily exponential, worst-case time.
Proving an exponential lower bound for every SAT decider would be stronger
than needed. Proving a bound for one solver, one branching rule, one variable
order, auxiliary-free CNF, monotone circuits, or a fixed proof system leaves
other deciders unaddressed. A separate theorem would be needed to turn such a
restricted lower bound into the quantified statement above.

For example, the CNF size of a projected parity relation can be exponential
while Gaussian elimination decides parity constraints efficiently. A lower
bound on that CNF representation therefore cannot be a lower bound on every
algorithm for the represented relation. Our existing
[parity note](parity_projection.md) is an explicit example of this distinction.

## 6. What tests and formal proofs establish

| Evidence | What it can establish | What it does not establish on its own |
|---|---|---|
| Independent exhaustive tests up to size `n0` | Correctness on that finite domain | Correctness or running-time behavior at unbounded sizes |
| Many fast benchmarks | Performance on the measured distribution and implementation | A uniform worst-case polynomial bound |
| A slowly growing or exponential family for one solver | A cost bound or obstruction for that solver, if proved for all sizes | A lower bound against all SAT algorithms |
| A Lean theorem about a fixed finite palette or a specified representation | The exact proposition checked by Lean, under its stated assumptions and trust model | A theorem about unrestricted SAT or all algorithms |
| A generic Lean correctness theorem | Correct outputs for the modeled procedure | A polynomial bound unless a cost model and cost theorem are also present |
| A small exact representation for each instance | An existence or size result | A fast uniform method to construct, manipulate, or decide it |

Finite testing cannot rule out a failure immediately beyond the test domain.
For any finite set of inputs, a lookup table can reproduce every answer; its
existence says nothing about a single efficient method for unbounded inputs.
For a formalization, inspect the quantified theorem statement, assumptions,
axioms, computational model, and the bridge to the executable code. The word
“verified” does not enlarge the theorem's scope.

For the mixed solver specifically,
[Formal/QuotientSearch.lean](../Formal/QuotientSearch.lean) formalizes exact
existential search through a quotient given valid lifts, a right inverse,
a covering enumeration, and a correct Boolean evaluator. Its input predicate
already has the form `linear x AND residual(observe x)`. Showing that the
original CNF factors through the observation map on the affine solution set
is an additional bridge to that theorem. The Python implementation of this
bridge, Gaussian elimination, encoding, and certificate checkers is not
formally verified by the abstract theorem. The separate `bitVectors_length`
lemma counts a Lean list; it is not a cost theorem for the Python solver.

## 7. Proof barriers: use the precise model, not a slogan

The following original papers are relevant if an argument begins to claim a
general separation or universal algorithmic theorem. They are not additional
benchmark gates, and none says that algebra, XOR, or experimentation is
forbidden.

| Result | Relevant limitation | Consequence for this project |
|---|---|---|
| Baker–Gill–Solovay [BGS] | There are oracle worlds with `P = NP` and with `P ≠ NP`. A proof that remains valid relative to every oracle cannot settle the unrelativized question. | Explain any oracle-relative extension before claiming a general theorem. Merely being a diagonal argument is not a sufficient diagnosis. |
| Razborov–Rudich [RR] | Under their hardness assumption, a circuit-lower-bound strategy satisfying the specified constructivity, largeness, and usefulness requirements is ruled out for the target general superpolynomial bounds. | This is conditional and concerns a defined class of circuit arguments. It is not a theorem that every intuitive or elementary proof fails. |
| Aaronson–Wigderson [AW] | Their algebraic oracle model gives an algebrization barrier to resolving P versus NP. | Using GF(2) arithmetic does not by itself place a proof in that model. A claim that the barrier applies needs a model-level argument. |

## Primary sources

- **[C]** Stephen Cook, [*The P versus NP Problem*](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf), official Clay Mathematics Institute problem description. Pages 1–2: machines, worst-case time, P, and NP; pages 3–5: reductions, completeness, and SAT; page 7: possible algorithmic and nonconstructive routes; appendix: machine model.
- **[BGS]** Theodore Baker, John Gill, Robert Solovay, [*Relativizations of the P = ? NP Question*](https://doi.org/10.1137/0204037), SIAM Journal on Computing **4**(4), 431–442 (1975). [Publisher page](https://epubs.siam.org/doi/10.1137/0204037).
- **[RR]** Alexander A. Razborov, Steven Rudich, [*Natural Proofs*](https://doi.org/10.1006/jcss.1997.1494), Journal of Computer and System Sciences **55**(1), 24–35 (1997). [Publisher abstract](https://www.sciencedirect.com/science/article/pii/S002200009791494X); [original-paper manuscript mirror](https://www1.karlin.mff.cuni.cz/~krajicek/rr.pdf).
- **[AW]** Scott Aaronson, Avi Wigderson, [*Algebrization: A New Barrier in Complexity Theory*](https://www.scottaaronson.com/papers/alg.pdf), author-hosted paper. See the definitions in Section 2 and the P versus NP barrier results in Section 5, especially Theorems 5.1 and 5.3.

The next research obligations are recorded in
[reverse_engineering.md](reverse_engineering.md).

## 8. Backward construction: make the hardness exponent outrun the verification cost

2026-11-10 JST. The user asked what is needed and requested constructing the
argument backward from that requirement. We choose one **sufficient** route to
P!=NP: a superpolynomial lower bound for general Boolean circuits computing a
single NP-complete language. This is stronger than the required uniform time
separation; it is not asserted to be necessary for P!=NP. The following is a
proof architecture with one explicitly missing construction, not a complete
proof, a new lower-bound theorem, or a novelty claim.

### A proved transfer lemma that fixes the previous quantifier gap

For each fixed positive integer k, suppose a language L_k has:

1. A specified NP verifier whose witness length **and total verification time**
   are O(n^(b_k)), with a fixed positive integer b_k. Here n is the original input bit length; time is
   not measured only in the certificate length. Constants may depend on k.
2. An unrestricted circuit lower bound: for infinitely many n, every circuit
   deciding L_k on all n-bit inputs has at least c_k*n^(a_k) gates, for some
   c_k>0 and a_k>0. Gates are fan-in-two AND/OR and fan-in-one NOT; fan-out and
   sharing are allowed. The bound covers all such circuits, not a solver,
   proof system, variable order, or particular circuit construction.
3. An unbounded ratio: for every D there is a fixed k with a_k/b_k>D.

Rounding any polynomial verification exponent b>=1 up to an integer multiplies
it by at most two, so this convention does not destroy an unbounded ratio.

**Transfer lemma.** These three premises imply SAT is not in P/poly, and hence
P!=NP. The languages L_k may differ: a costed reduction, not a quantifier swap,
transfers their bounds to one fixed SAT language.

**Proof.** Use the locally constructible near-linear Cook-Levin reduction
[W, Theorem 3.1]. Applied to the time-O(n^(b_k)) nondeterministic verifier, it
constructs an equivalent 3-CNF of encoded length n^(b_k+o(1)) in
n^(b_k+o(1)) deterministic time. The o(1) absorbs fixed polylogarithmic factors;
k is fixed before letting n grow. A standard computation-to-circuit simulation
gives reduction circuits of n^(b_k+o(1)) gates as well. This charges both writing
the formula and constructing its contents; no succinct-input shortcut is used.

For an exact fixed-length composition, use SAT_pad: a self-delimiting ordinary
3-CNF encoding followed by ignored zero padding, with malformed encodings
rejected. It is polynomially equivalent to ordinary SAT and NP-complete. Pad
the reduction output to a length M_k(n)=n^(b_k+o(1)) depending only on n and k,
not on x. Reading and producing this padding has the same charged bound.

Suppose SAT_pad has circuits of size O(M^d), for one fixed d>=1. Compose its
length-M_k(n) circuit with the reduction circuit. The resulting circuit for
L_k on length n has size

\[
 O\bigl(n^{b_k+o(1)}+M_k(n)^d\bigr)
       =n^{d b_k+o(1)}.
\]

Choose k so that a_k>d b_k. This k is a constant for the contradiction; it
need not be part of any input. Let delta=(a_k-d b_k)/2>0. For all sufficiently
large n, the composed size is O(n^(d b_k+delta))=o(n^(a_k)), contradicting
the infinitely-often lower bound in premise 2. Thus SAT_pad is not in P/poly.
Since SAT_pad reduces to ordinary SAT in polynomial time, polynomial-size
circuits for SAT would give polynomial-size circuits for SAT_pad. Therefore
SAT is not in P/poly. Finally P is contained in P/poly, so SAT is not in P
and NP-completeness gives P!=NP. QED.

This lemma does not establish any of its input lower bounds. For example,
an effective family of verifiers all running in O(n^3), with general-circuit
lower bounds Omega(n^k) for unbounded k, would meet it. Merely allowing the
verification exponent to grow faster than the lower-bound exponent does not.

### A concrete seed and the missing amplification lemma

A seed is available without any conjecture. The n-input parity function has a
linear-time verifier (just compute parity). Every fan-in-two circuit computing
it has at least n-1 gates: all n inputs are essential, and the connected fan-in
graph of the output with s gates has at least n+s-1 edges and at most 2s edges.
Thus a_0=b_0=1 is a valid seed, with lower-bound constant 1/2 for n>=2.
This familiar linear bound concerns general circuits, but its exponent ratio
is only one. Parity is in P.

There is an immediate constraint on any proposed operation: if its purported
O(n^b) verifier actually decides the language without a witness, the standard
time-to-circuit simulation already supplies n^(b+o(1))-size circuits. It cannot
also have an infinitely-often Omega(n^a) lower bound with a>b. Merely processing
easy functions in a more elaborate way cannot provide the first increase.

One possible missing lemma would be an explicit transformation A with a fixed
rho>1 that takes a specified verifier and a proved general-circuit lower bound,
and produces another specified NP verifier plus a proved general-circuit bound
with

\[
        \frac{a_{j+1}}{b_{j+1}}
          \ge \rho\,\frac{a_j}{b_j}.
\]

The output must meet premises 1 and 2 above, including uniform verification,
the complete circuit model and the infinitely-many-lengths quantifier. The
transformation may incur a large constant description cost for each fixed j,
but cannot hide superpolynomial witness processing behind an oracle. Iterating
it from parity would give a_j/b_j>=rho^j. The transfer lemma would then give
P!=NP. This closes the logical implication **if A exists with those proofs**.
No such transformation or proof has been obtained here. Introducing its name
is not progress on the missing lower bound, nor is this amplification mechanism
claimed necessary for every possible solution of P versus NP.

### Actual attempts to construct the amplification

**Padding fails the required accounting.** Pad n-bit inputs to length
N=Theta(n^p), for a fixed p>=1. Restricting a circuit for the padded language
to the prescribed padding recovers a circuit for the original language, so the
supplied lower bound becomes Omega(N^(a/p)). The available verifier checks the
padding and the original witness in time O(N+n^b), with exponent max(1,b/p).
The ratio supplied by this construction is therefore

\[
       \frac{a/p}{\max(1,b/p)}
          =\frac{a}{\max(p,b)}\le\frac{a}{b}.
\]

Padding alone does not amplify this pair of bounds. A different improved
verifier for the padded problem would require its own new argument.

**Independent conjunction does not supply amplification either.** Take
t=n^r independent n-bit instances, r>=0, and ask that all belong to L.
The new input length is N=Theta(tn), and concatenating the witnesses costs
t*n^b=N^((r+b)/(r+1)) up to encoding factors. Even if we *grant* the optimistic
direct-sum lower bound t*n^a, the resulting ratio is

\[
 \frac{(r+a)/(r+1)}{(r+b)/(r+1)}
   =\frac{r+a}{r+b}
   =\frac{r}{r+b}\cdot1+\frac{b}{r+b}\cdot\frac{a}{b}.
\]

It lies between one and the old ratio, so cannot yield rho>1 from the parity
seed. No general direct-sum lower bound is being asserted. For this seed the
failure is unconditional: a two-bit XOR uses four AND/OR/NOT gates, so the
conjunction of t independent n-bit parities has a circuit with
4t(n-1)+(t-1)<4N gates. The actual candidate still has linear-size circuits.

**Connecting parity constraints by expansion also fails for this candidate.**
On a fixed connected graph G, assign an edge bit to each edge and require that
the XOR of incident edge bits at each vertex equal its charge chi_v. Summing
all equations proves that SAT requires XOR_v chi_v=0. For sufficiency, set
non-tree edges to zero in a spanning tree and eliminate leaves, choosing each
leaf's parent-edge value to satisfy its equation and updating the parent
charge. The final root equation holds exactly when the total charge is even.
Thus as a function of q charge bits, satisfiability is simply even parity,
with at most 4(q-1)+1 gates, regardless of the graph's expansion. This does
not address arbitrary CNFs; it rejects this explicit proposed amplification.
Proof-system hardness on these inputs cannot replace premise 2.

### Applying the criterion to the previous literature route

The conditional conclusion of Murray-Williams [MW, Theorem 1.1] supplies
a_k=k and a verifier-time exponent b_k=ceil(c k^4/epsilon). These stated bounds give

\[
          a_k/b_k\le\epsilon/(c k^3),
\]

which is bounded and tends to zero. They do not meet premise 3. This is not a
claim that no sharper verifier or lower bound exists; it specifies what the
quoted theorem does and does not supply. Padding the verifier time down to a
fixed degree also scales down the lower bound, as calculated above.

**Status.** The seed, the transfer implication, and the failures of these
three attempted constructions are justified. The amplification lemma remains
unproved, and no family meeting the unbounded-ratio condition has been
constructed. This is a precise conditional proof architecture; it does not
qualify as a provisional complete-proof candidate. No numerical experiments
or new Lean verification are claimed for this argument.

Sources read, already used in the previous investigation:

- **[W]** R. Ryan Williams, [*Improving exhaustive search implies
  superpolynomial lower bounds*](https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf),
  SIAM Journal on Computing 42(3), 1218-1244 (2013), Theorem 3.1 for the
  near-linear nondeterministic-time-to-3SAT reduction. The circuit composition
  and exponent accounting above are elementary deductions, not a new theorem
  attributed to that paper.
- **[MW]** Cody D. Murray and R. Ryan Williams, [*Circuit Lower Bounds for
  Nondeterministic Quasi-Polytime: An Easy Witness Lemma for NP and NQP*](https://people.csail.mit.edu/rrw/easy-witness-nqp.pdf),
  STOC 2018, Theorem 1.1. Its circuit-algorithm hypothesis remains a hypothesis;
  quoting its conclusion does not establish the required lower bounds here.

## 9. Continuation: test whether existential witnesses amplify the lower bound

2026-11-10 JST. The previous section did not construct the missing amplifier.
We now test a concrete possible mechanism: attach witnesses to a function with
a proved circuit lower bound, preserve that bound in the verifier, and try to
transfer it to the language obtained by existentially hiding the witnesses.
The transfer fails even with unique, exponentially sparse witnesses. The
following arguments are elementary checks of this proposed mechanism, not
novel circuit lower bounds.

### The previous target is equivalent to a stronger separation problem

Section 8 proves that its unbounded-ratio condition implies NP is not contained
in P/poly. The converse holds too. If NP is not contained in P/poly, then SAT
is not in P/poly, because every NP language reduces to SAT in polynomial time.
Fix one SAT verifier with witness and time bound O(n^B), for a positive integer
B. For every positive integer k there must be infinitely many lengths n with

\[
                     C(\mathrm{SAT}_n)\ge n^{kB}.
\]

Otherwise that degree would bound all sufficiently large lengths; finitely
many exceptions could be absorbed in a constant, placing SAT in P/poly.
Take L_k=SAT, b_k=B, a_k=kB and c_k=1. This supplies exactly the previous
premises, with ratio k. Thus the condition is equivalent to NP not contained
in P/poly, not a demonstrated easier intermediate problem. Its useful content
is the accounting rule for proposed constructions. It is still only a
sufficient route to P!=NP; no equivalence between P!=NP and NP not contained
in P/poly is asserted.

### A candidate that preserves verifier hardness but loses decision hardness

Let f be any Boolean function on n bits, and let q>=1. Introduce an additional
ordinary input bit z and witness bits w_1,...,w_q. Define

\[
 V_f(x,z,w)=z\land [w_1=f(x)]\land
                  \bigwedge_{i=2}^{q}\neg w_i,
 \qquad L_f(x,z)=\exists w\ V_f(x,z,w).
\]

Here C counts fan-in-two AND/OR and unary NOT gates, with input wires and
constant wires free. Allowing free constants does not change P/poly or the
exponent criterion. Encode z first if measuring sequential input access.

This is a uniform construction when f is uniformly computable; it does not
assume access to an oracle for a hard function. The attempt would use the
following genuine facts as evidence for amplification:

- Restricting z=1, w_1=1 and all other witness bits to zero recovers f.
  Therefore C(V_f)>=C(f), by constant substitution and gate simplification.
- Every YES input has exactly one witness, namely (f(x),0,...,0). Every NO
  input has none. Half the ordinary inputs are YES and half are NO.
- On every YES input, a uniformly random q-bit witness succeeds with
  probability exactly 2^(-q).

Nevertheless, the projected language is exactly

\[
                         L_f(x,z)=z.
\]

It has a zero-gate circuit consisting of an input wire. This proves that a
lower bound for the verifier, uniqueness of witnesses, and exponentially
small witness density together do not imply a lower bound for the existence
decision. This rejects the proposed inference, not every existential
construction or the unproved amplifier in Section 8.

The counterexample has an explicit resource bound. Equality between w_1 and
f(x) uses four AND/OR/NOT gates for XOR followed by NOT; conjunction with z
uses one more. Each additional witness bit adds one NOT and one AND. Hence

\[
                       C(V_f)\le C(f)+2q+4.
\]

For the parity seed and q=n, this is at most 6n gates, since parity has a
4(n-1)-gate construction. The verifier runs in O(n) bit time, has a lower
bound of n-1 gates, and has exactly one successful witness among 2^n choices
on each YES input. Yet deciding the language just reads z. These statements
hold at every n>=1, not merely in the finite check below. The verifier cost
is measured against n+1 ordinary input bits, which changes no exponent.

**Attempted repair: constrain the first witness bit.** Setting w_1=1 makes
the projection z AND f(x), which is computable with C(f)+1 gates. More
generally, forcing w_1=g(x) makes it z AND [g(x)=f(x)], with at most
C(f)+C(g)+6 gates. A linear-size g and the parity seed therefore still give
a linear-size decision circuit. Neither repair creates the first exponent
increase. Using a g with an unproved lower bound would import the missing
hardness rather than derive it.

### Two bounds that a replacement construction must respect

**A cheap successful-witness selector gives a cheap decision circuit.** Let
V_n(x,w) have s(n) gates. Suppose a multi-output circuit W_n(x) of t(n) gates
has the property that whenever any witness is accepted, W_n(x) is accepted.
Then

\[
       [\exists w\ V_n(x,w)] = V_n(x,W_n(x)),\qquad
       C(L_n)\le s(n)+t(n).
\]

On NO inputs every witness is rejected; on YES inputs the selector's premise
gives acceptance. Composition proves the size bound, allowing sharing and
counting the whole selector. Even nonuniform selector circuits suffice for
this upper bound. In the candidate above W_n(x,z)=(f(x),0,...,0), so the
selector is already available from the seed. Conversely, a difficult selector
would not by itself prove difficult decision: L_f=z for arbitrary f.

**Short witnesses can be enumerated.** If there are q(n) witness bits, fix
each possible witness in a copy of V_n and OR the results. This gives

\[
                  C(L_n)\le 2^{q(n)}s(n)+2^{q(n)}-1.
\]

For s(n)<=n^(b+o(1)) and q(n)<=c log_2(n)+O(1), the upper bound is
n^(b+c+o(1)). It precludes an infinitely-often Omega(n^a) lower bound with
a>b+c. A uniform polynomial-time verifier with O(log n) witness bits also
gives a polynomial-time decider by this enumeration. This is a bound on the
specified construction, not a ban on all polynomial-length witnesses;
larger q merely removes this particular cheap enumeration and supplies no
lower bound. The q=n counterexample demonstrates that distinction.

### Bounded independent check and decision

In addition to the all-size proofs, the following check was run over every
Boolean function on n=1,2,3 inputs and q=1,2,3,4. It checked 276 functions,
1,104 relations, 127,200 verifier rows, 16,960 fibers and 8,480 restrictions.
All checks passed. This enumerates truth tables, not all circuits, and does
not provide an asymptotic circuit lower bound or a Lean verification.

```python
from itertools import product
for n in range(1, 4):
    for values in product((0, 1), repeat=1 << n):
        for q in range(1, 5):
            def verify(x, z, w):
                return z == 1 and w[0] == values[x] and not any(w[1:])
            for x in range(1 << n):
                for z in (0, 1):
                    accepted = [w for w in product((0, 1), repeat=q)
                                if verify(x, z, w)]
                    assert len(accepted) == z
                    if z:
                        assert accepted == [(values[x],) + (0,) * (q-1)]
                assert verify(x, 1, (1,) + (0,) * (q-1)) == bool(values[x])
```

Stop this proposed amplification mechanism and its two repairs. A replacement
must establish a lower bound for the projected decision function itself;
counting witnesses, lower-bounding the verifier, or lower-bounding a particular
search procedure does not supply it. No such projected-function bound was
obtained here. The generic amplification route remains an unfulfilled
specification, and there is still no complete P-versus-NP proof candidate.

## Reporting a possible resolution

Flag a provisional candidate before final verification when there is a concrete all-input algorithm and a substantive argument that every stage has fixed polynomial bit cost, or a concrete lower-bound argument covering every deterministic polynomial-time decider for a language in NP. Identify the central lemma, what is checked, what is still open, and the likeliest counterexample. A conditional statement that merely restates the missing P versus NP claim, passing finite tests, faster performance on a family, a restricted representation lower bound, or a successful ETH endpoint rebuild alone does not trigger this label.
