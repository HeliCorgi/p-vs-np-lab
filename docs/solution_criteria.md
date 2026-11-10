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

## 10. Continuation: construct the hard decision function by counting

2026-11-10 JST. The next attempt addresses the decision function directly:
count small circuits, choose a truth table outside their range, and try to
make its bits an NP language. This is an audit of elementary counting and
canonical selection, not a new circuit lower bound. It does not reopen the
stopped streaming-state argument.

### Counting gives hard functions but an easy completion predicate

Let m be the number of inputs to a Boolean function and N=2^m its truth-table
length. Use the AND/OR/NOT basis and free constants of Section 9. For a gate
budget s, put

\[
 w=\lceil\log_2(m+s+2)\rceil,\qquad
 \ell=s(2+2w)+w.
\]

Every circuit of at most s gates has a description of length ell: pad to s
gates, use two operation bits and two w-bit wire indices per gate, and a w-bit
output index. A NOT gate ignores its second index; invalid descriptions are
discarded. Therefore the set E of easy truth tables has size at most 2^ell.
Whenever ell<N, some truth table has circuit complexity greater than s.

For a prefix p of r<=N truth-table bits, consider the actual decision predicate

\[
 H_{m,s}(p)=[\exists T\in\{0,1\}^{N}:T\text{ extends }p
                                      \text{ and }C(T)>s].
\]

There are exactly 2^(N-r) extensions of each p. Thus

\[
       2^{N-r}>|E|\ \Longrightarrow\ H_{m,s}(p)=1
                        \text{ for every prefix of length }r.
\]

In particular, N-r>ell is a sufficient condition. For s=m^k and r polynomial
in m, it holds at all sufficiently large m. The attempted predicate is then
constant YES on the entire prefix domain, despite every accepted prefix
having a hard completion. The same counting proof holds for prescribing r
distinct positions instead of a prefix. Existence of a hard completion alone
does not produce a hard decision about those prescriptions.

At r=N the predicate instead asks whether the supplied table itself needs
more than s gates. For 0<=s<=N, this is the complement of explicit-table MCSP
and is in coNP: a circuit of at most s gates has polynomial description length
in N and can be checked against all N entries in polynomial time. No
coNP-completeness or NP membership is assumed for this predicate.

### Repair: pick one table consistently, then charge its selection

At lengths with ell<N, define T* to be the lexicographically first hard table,
using inputs 00...0 through 11...1 as the table order. Define a language's
length-m characteristic function by D_m(x)=T*[x]. Its circuit complexity is
greater than s **by construction**. Unlike an arbitrary hard-completion
witness, T* is the same table for every queried x. For the budget families
below, ell<N eventually; define D_m to be zero at the other, finitely many
lengths. The lower bounds for D and its short-tail representation below
concern lengths with ell<N.

There is a finite algorithm: enumerate tables in lexicographic order and
test each against all circuits within the budget. No polynomial cost in m
follows. Guessing the entire table already uses N=2^m bits on an m-bit input.
Checking it against all circuits by enumeration is also not a polynomial-time
verification in m. This does not exclude a shorter representation. We next
construct one, rather than treating the full-table length as an unavoidable
obstacle for every encoding.

**A further repair succeeds in shortening the description.** Interpret a
truth-table word as a binary integer, with its first entry most significant.
Among the first |E|+1 words some word is hard. Therefore the lexicographically
first hard table has numerical value at most |E|<=2^ell. It has the form

\[
                  T^*=0^{N-t}u,\qquad t=\ell+1,
\]

where u has t bits. For a fixed budget s=m^k, this is a polynomial-length
description O(m^k log m), together with m. The longer zero prefix is implicit.
Thus lack of a polynomial-length table description is **not** the remaining
obstacle at any fixed polynomial gate budget.

It also gives an explicit nonuniform circuit upper bound. Put q=ceil(log_2 t)
and pad the tail to 2^q entries with leading zeros. On inputs whose first m-q
bits are all one, look up the last q bits in that tail; return zero otherwise.
A binary multiplexer tree uses at most 4(2^q-1) AND/OR/NOT gates. The prefix
test and final conjunction cost at most m gates. Consequently

\[
             s<C(D_m)\le 8t+m=O(s\log(m+s)+m).
\]

The tail's values are hardwired, so this is a size upper bound without an
efficient uniform constructor. In particular, each fixed-k language obtained
this way is unconditionally in P/poly, despite exceeding the particular
budget m^k. More generally, **any** explicit-tail encoding of a function with
C(f)>s must have t>(s-m)/8 by the same circuit construction. For s>=2m this
forces t>s/16. Guessing and processing such a complete tail in the bit model
therefore costs Omega(s), even if its remaining validation were free. The
explicit-tail verifier cannot turn a supplied m^k lower bound into an exponent
ratio greater than one. This is a limitation of this representation, not of
all possible certificates for individual bits.

**What remains to verify is not an existential bit lookup.** Let T_u be the
function described by the zero prefix and a proposed short tail u. Hardness
requires

\[
       \forall\text{ circuits }C\text{ of size at most }s\quad
       \exists x\in\{0,1\}^m:\ C(x)\ne T_u[x].
\]

For fixed k and s=m^k all descriptions in this formula have polynomial
length in m, and a proposed mismatch is efficiently checkable. The formula
has a universal circuit quantifier followed by an existential input
quantifier: it supplies a Pi_2^P test for the tail, not an NP verification.
No claim that this predicate lies outside NP is being made.

There is an unconditional polynomial-hierarchy upper bound for selecting
the canonical tail. Supply m and s in unary to an oracle query, and ask
whether a specified tail prefix has an extension u satisfying the displayed
hardness condition. Its quantifiers are `exists u, forall C, exists x`, so
this one query language is in Sigma_3^P. Invalid circuit descriptions are
ignored. Greedily query the zero extension at each tail position; this selects
the first hard table in polynomially many calls for each fixed k. Therefore
the resulting fixed-k bit language is in P^(Sigma_3^P), as well as P/poly.
We have not reduced this algorithm or its certificates to NP. Under P=NP
the hierarchy collapses and each such language is in P; its algorithm's
polynomial degree may depend on k, consistently with its m^k circuit lower
bound. This directly checks the quantifier issue from the previous turns.

To make the missing cost particularly explicit, pad an H query to length
Theta(N), and include m,s,p with 0<=s<=N. In this **padded** encoding H belongs
to Sigma_2^P: existentially guess the N-bit T, universally quantify a circuit
description of O(N log N) bits, and deterministically check that the circuit
is invalid or disagrees somewhere with T. Scanning all N inputs is polynomial
in the padded length. This does not establish Sigma_2^P membership in the
compact encoding whose only data are m,s and a short p, and it does not put
D in NP.

**The superpolynomial-budget variant still exceeds NP's established resources.** Set
s_m=2^floor(m/2). The description bound has ell=O(m*2^(m/2))<2^m for all
sufficiently large m. Choose T* at those lengths and the zero table at the
finitely many lengths where this inequality fails. If P=NP, the padded H
predicate is in P. One way to see this is that explicit-table MCSP is in NP,
so its complement is in P under the assumption; guessing T then gives an NP
predicate, which is again in P under the same assumption.

Construct T* one bit at a time. Given a prefix p that has a hard completion,
choose zero next when H(p0) is true, and one otherwise. At least one child has
a hard completion. Induction gives the lexicographically first hard table
after N queries, each of padded length O(N). The whole construction therefore
costs N^O(1)=2^O(m), including all padding and output bits. It supplies

\[
 \mathrm P=\mathrm{NP}\quad\Longrightarrow\quad
 \text{this }D\in\mathrm E=\mathrm{DTIME}(2^{O(m)}),\qquad
 C(D_m)>2^{\lfloor m/2\rfloor}\text{ eventually}.
\]

This is a standard kind of conditional counting construction, not a new
separation claim. It shows that even this strong circuit lower bound for the
constructed language would be compatible with P=NP: the proved membership
under that assumption is in E, not NP. The earlier Williams source [W,
Section 1.2] discusses the related implication P=NP => EXP not contained in
P/poly; the particular costed construction above is proved here rather than
attributed to a theorem number in that paper.

Padding the m-bit input to N=2^m bits does not fix the Section 8 exponent
budget: the displayed lower bound s_m becomes only Theta(sqrt(N)) in that new
input length. Providing the full truth table as input also incurs N bits of
representation and its explicit verification cost; it does not itself
transfer a lower bound to the new decision problem. These observations concern
these supplied bounds and encodings; they do not rule out a different short
certificate or a stronger lower bound proved by another argument.

### Exact finite control, and the decision on this attempt

For m=3 we enumerated all general circuits with at most three gates, allowing
sharing, constants and all outputs. The existing
[semantic DAG enumerator](../experiments/mcsp_update_gate.py) was cross-checked
against a separate direct enumeration of gate sequences without merging
states. There are 35 one-gate sequences, 1,680 two-gate sequences and 105,840
three-gate sequences when binary inputs are unordered. Their reachable
function sets agree at every budget. All 2,044 budget/prefix pairs were then
classified, including the empty and full prefixes.

| Gate budget s | Easy tables | Hard tables | First prefix length with both YES and NO | First hard table |
|---|---:|---:|---:|---|
| 0 | 5 | 251 | 8 | `00000001` |
| 1 | 14 | 242 | 8 | `00000001` |
| 2 | 40 | 216 | 7 | `00000010` |
| 3 | 84 | 172 | 6 | `00000110` |

These finite counts check the distinction between a hard table and the
predicate of extending a prefix to some hard table. They establish no
asymptotic NP lower bound. The table and the counting inequality can be
reproduced from the repository root with this Python snippet:

```python
from experiments.mcsp_update_gate import small_circuit_catalog
costs, _ = small_circuit_catalog(3, 3)
for s in range(4):
    easy = {t for t, c in costs.items() if c <= s}
    hard = set(range(256)) - easy
    profile = []
    for r in range(9):
        yes = {t & ((1 << r) - 1) for t in hard}
        profile.append(len(yes))
        if (1 << (8-r)) > len(easy):
            assert len(yes) == 1 << r
    word = lambda t: ''.join(str((t >> i) & 1) for i in range(8))
    first_mixed = next(r for r, count in enumerate(profile)
                       if 0 < count < 1 << r)
    print(s, len(easy), len(hard), first_mixed, word(min(hard, key=word)))
```

The short-tail circuit construction was also executed independently of the
catalog: all 546 tails of lengths 1 through 2^m at m=1,2,3 were compiled and
their 4,212 truth-table rows checked with the existing gate evaluator. Every
circuit met the exact count `4(2^q-1)+max(0,m-q)` and hence the proved upper
bound. This includes a one-entry tail, a full table and non-power-of-two tail
lengths. The check is reproducible as follows; it is not a general SAT solver.

```python
from itertools import product
from experiments.mcsp_update_gate import BooleanCircuit
for m in range(1, 4):
    for t in range(1, (1 << m)+1):
        q = (t-1).bit_length()
        for tail in product((0, 1), repeat=t):
            c = BooleanCircuit(m)
            def lookup(values, level=0):
                if len(values) == 1:
                    return values[0]
                mid = len(values)//2
                lo = lookup(values[:mid], level+1)
                hi = lookup(values[mid:], level+1)
                select = 2+m-q+level
                return c.gate('OR', c.gate('AND', c.gate('NOT', select), lo),
                              c.gate('AND', select, hi))
            out = lookup((0,)*((1 << q)-t)+tail)
            if m > q:
                guard = 2
                for j in range(1, m-q):
                    guard = c.gate('AND', guard, j+2)
                out = c.gate('AND', guard, out)
            assert c.table(out) == [0]*((1 << m)-t)+list(tail)
            assert len(c.gates) == 4*((1 << q)-1)+max(0, m-q)
            assert len(c.gates) <= 8*t+m
```

Stop these constructions as claimed NP lower-bound proofs. The arbitrary
completion predicate is constant on the intended short-input range. Canonical
selection does define a hard function, and the short-tail repair succeeds for
fixed polynomial budgets, but it supplies no NP verifier for the selected
bits and no exponent amplification from reading the explicit tail. Raising
the gate budget to superpolynomial raises that tail cost too. The unproved
NP-membership step must not be treated as an available interface lemma.
There is still no complete P-versus-NP proof or surviving complete-proof
candidate; no new Lean verification is claimed.

## 11. Bit certificates: sample interpolation and canonical soundness

2026-11-10 JST. We continued the missing bit-verification step from Section
10. The concrete candidate supplies a small set of truth-table values as
evidence of circuit hardness, together with the value of the requested bit.
Two independent requirements must hold: the observations must exclude small
circuits, and they must refer to the selected canonical function. Neither
requirement can be dropped. The following interpolation argument and finite
countercheck audit this candidate; they are not new NP lower bounds.

### Any small collection of samples has an easy completion

Let m>=1 and let r distinct m-bit inputs have consistent prescribed Boolean
values. There is a circuit of at most 2mr gates agreeing with all of them.
This holds for arbitrary sampled positions, not just the contiguous tail of
Section 10. As before, use binary AND/OR, unary NOT and free constants.

**Construction and proof.** For each prescribed one at an input a, form the
point indicator

\[
             \delta_a(x)=\bigwedge_{j=1}^{m}
                    \begin{cases}x_j,&a_j=1,\\\neg x_j,&a_j=0.\end{cases}
\]

It uses at most m NOT gates and m-1 AND gates. OR the p indicators for all
prescribed ones. If p=0 use the zero circuit. Otherwise the gate count is at
most p(2m-1)+(p-1)=2mp-1<=2mr. The result is one exactly at the prescribed
positive points, so it also respects every distinct prescribed zero. This
is a uniform construction in polynomial time in the explicit sample list;
no SAT oracle, unavailable circuit or promised extension is used.

Grant even that all reported values really come from the intended function.
A certificate that concludes C(f)>s **solely by excluding every size-s
circuit consistent with those samples** must therefore have

\[
                    r>\frac{s}{2m}.
\]

For a literal list containing each m-bit address and its one-bit value, its
length is at least

\[
             r(m+1)>\frac{s(m+1)}{2m}>s/2.
\]

Thus this explicit-list mechanism already spends Omega(s) bits before any
hardness validation. At a supplied lower-bound scale s=m^k, reading and
processing this certificate cannot give the exponent ratio greater than one
needed to amplify Section 8's seed. The inequality is independent of how
the sampling positions are selected. The address-length bound is specific
to the literal-list encoding; a compressed description or an unrelated
mathematical proof is not ruled out. The interpolation statement itself
also gives an r-query obstruction for a deterministic, always-correct test
whose only information about the table is those r values, including
adaptively chosen values.

### Even correct hardness evidence need not prove the selected bit

Suppose a proposed certificate for D_m(x)=1 instead supplies a table T with
T[x]=1 and proves C(T)>s. This still omits why T is the lexicographically
first hard table. Granting a perfect hardness check does not fix its
soundness as a verifier for D.

The counting inequality in Section 10 gives an all-size falsifier. When
N-1>ell, there is a hard table with either value at **every** chosen input x:
each prescribed value leaves 2^(N-1)>2^ell possible tables. The proposed
existential test would therefore accept every x. But the canonical table's
leading N-ell-1 entries are zero, including its first entry. It is not the
all-one function. The witness is for the wrong table, even though its own
hardness and reported bit may be correct.

A concrete finite instance uses three inputs and a three-gate budget. Exact
enumeration gives the first hard table `00000110`, while `10000001` is another
hard table. The second table has the opposite first bit. A verifier accepting
some hard table with the claimed first bit would therefore accept a false
claim about the first table. This example concerns the finite canonical
table whenever it exists; the arbitrary small-length exceptions in the
asymptotic language definition do not enter the check.

Replacing the sample list by one common representation with a fast decoder
also has a cost constraint: if a representation is hardwired and all bits
can be decoded in time T, with T at least the input and representation lengths,
the standard simulation supplies circuits of O(T log T) gates. It cannot
support a lower-bound exponent larger than the decoder-time exponent.
This statement does **not** apply to arbitrary NP proofs that vary with the
queried input; those need not form a common fast decoder. Such a sound
bit-specific verifier for the selected function has not been constructed.

### Executed checks and decision

The interpolation construction was run for every partial truth table on
m=1,2,3 inputs, using an unspecified/zero/one choice at each position. All
6,651 partial tables were extended to circuits; all 35,220 specified values
and all gate bounds passed. The empty sample, all-zero, all-one and mixed
sample cases are included. The check uses the existing gate evaluator:

```python
from itertools import product
from experiments.mcsp_update_gate import BooleanCircuit
cases = specified = 0
for m in range(1, 4):
    for partial in product((-1, 0, 1), repeat=1 << m):
        c = BooleanCircuit(m)
        terms = [c.point_indicator(x) for x, value in enumerate(partial)
                 if value == 1]
        out = terms[0] if terms else 0
        for term in terms[1:]:
            out = c.gate('OR', out, term)
        actual = c.table(out)
        r = sum(value != -1 for value in partial)
        assert all(value == -1 or actual[x] == value
                   for x, value in enumerate(partial))
        assert len(c.gates) <= 2*m*r
        cases += 1
        specified += r
assert (cases, specified) == (6651, 35220)
```

The false-bit example is independently reproducible using the exact circuit
catalog, whose agreement with raw gate-sequence enumeration was checked in
Section 10:

```python
from experiments.mcsp_update_gate import small_circuit_catalog
costs, _ = small_circuit_catalog(3, 3)
hard = set(range(256)) - set(costs)
word = lambda t: ''.join(str((t >> i) & 1) for i in range(8))
canonical = min(hard, key=word)
other = sum(int(bit) << i for i, bit in enumerate('10000001'))
assert word(canonical) == '00000110'
assert other in hard and (canonical & 1) == 0 and (other & 1) == 1
```

These finite checks validate constructions and the counterexample; they do
not establish an asymptotic separation or replace the interpolation proof.
No Lean verification is claimed.

**Research decision.** Park the canonical-hard-table construction as a main
P-versus-NP route. It supplies hard functions and some compact descriptions,
but the full-tail and explicit-sample certificates lose the required cost
advantage, while merely certifying some hard table gives unsound answers
about the selected bits. This is a practical stopping decision under the
user's early-pruning instruction, not an impossibility theorem for all NP
certificates or all counting methods. Reopening this route requires a
specified sound bit verifier and a resource argument that addresses these
defects. No such verifier or new complete-proof candidate was obtained.

## 12. A P=NP attempt: bounded-clause elimination and two-variable lookahead

2026-11-10 JST. After parking canonical hard tables, we changed to an
algorithmic route: repeatedly simplify a SAT instance while controlling the
size of its explicit representation. We test ordinary Davis-Putnam variable
elimination with a nonincreasing clause budget, including a two-variable
repair that may temporarily increase the budget. These are established
operations, not a new SAT algorithm. See the Davis-Putnam reference and the
different earlier representation experiment in [event_projection.md](event_projection.md).

### The exact operation and the sufficient progress claim

Write a CNF as

\[
 F=F_0\land\bigwedge_i(x\lor A_i)\land\bigwedge_j(\neg x\lor B_j).
\]

Eliminating x replaces its parent clauses by all resolvents A_i OR B_j,
retaining F_0. Delete tautologies, duplicates and clauses containing another
clause as a subset. The result G satisfies G(y) iff some x satisfies F(x,y).
Indeed a satisfying x makes every resolvent true. Conversely, if all A_i
are true choose x=0; otherwise a false A_i forces all B_j true through the
resolvents, and x=1 works. Empty parent families are handled by the same
argument. The simplifications preserve the Boolean function exactly.

The candidate accepts a block of one or two occurring variables only if,
after eliminating the whole block and simplifying, the clause count does
not increase. For a pair, temporary growth after the first elimination is
allowed. Search all such blocks. No clauses means SAT; an empty clause means
UNSAT; if neither occurs and no block is acceptable, the procedure is stuck,
not UNSAT. A SAT assignment can be lifted by reversing the exact eliminations.

**Conditional cost argument.** Renumber occurring variables densely first.
Let n and M be the initial variable and clause counts. No new variable is
introduced; accepted states have at most M clauses of width at most n.
One trial elimination produces at most O(M^2) clauses, and two produce at
most O(M^4), before simplification. Even pairwise subset checking on these
explicit clauses has polynomial bit cost. Scanning O(n^2) blocks per round
and accepting at most n rounds remains polynomial. Recording the accepted
eliminations and reversing them also uses polynomial resources. Clause widths,
wire-name bits and failed trials are charged; a decreasing variable count
alone would not establish this bound.

Thus the missing progress claim would suffice: **every nonterminal instance
has an acceptable one- or two-variable block.** We do not assume it. The
following connected SAT family refutes it for every choice of block.

### An explicit family where every single elimination increases the budget

For every integer p>=11, use 3p variables A_i,B_i,C_i, with i modulo p.
For each i and t=0,...,5 include the clause on

\[
                         A_i,\ B_{i+t},\ C_{i+2t},
\]

with all three literals positive when t<3 and all three negative otherwise.
Call the resulting formula F_p. It has 6p clauses and 18p literal occurrences.
Setting every A_i true and every B_i false satisfies it, whatever the C_i
values. This supplies an easily checked witness, not general SAT hardness.

Each variable occurs positively three times and negatively three times.
Any two distinct clauses share at most one variable: equality of an A/B pair
fixes i,t; equality of a B/C pair fixes t and then i; equality of an A/C pair
forces 2(t-t')=0 modulo p, and |2(t-t')|<=10<p. The incidence graph is
connected: the t=0 clauses join the three variables at each index, while the
t=1 clauses join successive indices. There are no units, pure variables,
tautologies, duplicates or subsumable original clauses.

For any variable x, its six incident clauses have pairwise disjoint remaining
two-variable sets. Its three positive and three negative parents therefore
produce nine distinct, nontautological four-literal resolvents, each with two
positive and two negative literals. No original three-literal clause, whose
literals all have the same sign, subsumes one. The new clauses do not subsume
one another. Hence every single elimination has the exact changes

\[
          \Delta\#\text{clauses}=9-6=3,\qquad
          \Delta\#\text{literal occurrences}=36-18=18.
\]

The conclusion is unchanged by any permutation of variables or consistent
negation of selected variables, because these preserve resolution,
tautology, duplication and subset relations.

### The two-variable repair also fails, even with temporary growth

**Nonadjacent pair.** If x,y occur in no common clause, their incident parent
sets are disjoint and eliminating one creates no occurrence of the other.
There are 18 four-literal resolvents replacing 12 clauses. Resolvents from
the two eliminations cannot coincide: their two positive literals would
then belong to two different original positive clauses, contradicting the
one-shared-variable property. All have two positive and two negative literals,
so original homogeneous clauses do not subsume them. The net increase is six.

**Adjacent pair.** Suppose the shared clause is x OR y OR z. The negative
shared-clause case follows by exchanging signs. Apart from this clause,
each of x and y has two positive and three negative parents. Eliminating
both variables yields:

- Six resolvents from x's other positive parents and its negative parents.
- Six from y's other positive parents and its negative parents.
- Nine clauses formed from z and the two negative remainders, one from an
  x-parent and one from a y-parent.

The first twelve have two literals of each sign. The last nine have z as
their only positive literal and three or four negative literals. They are
nontautological: no negative parent can also contain z without sharing two
variables with the original shared clause.

For completeness, no simplification erases these counts. Within either
negative-parent family the two-element remainder sets are disjoint; across
families they intersect in at most one element. Their nine pairwise unions
are distinct and form an antichain. To see this, an inclusion between unions
with different first indices would force that first two-element set into a
single opposite-family set, contradicting their intersection bound; if the
first indices agree but the second differ, use disjointness of the second
family to obtain the same contradiction. Thus the last nine clauses cannot
subsume one another. Their sign counts also preclude subsumption with the
first twelve. Those first twelve are distinct by the positive-parent
intersection argument used above. A surviving original negative clause
cannot be contained in a last-family clause: three negative literals from
two two-element remainders would share two with one original parent. Original
positive clauses cannot be contained in it either.

All 21 derived clauses therefore survive, replacing 11 parents. The increase
is ten. This is the final count after both eliminations, in either order;
the argument is not merely a rejection of the intermediate step. In total,

\[
 \Delta\#\text{clauses}=
 \begin{cases}
  3,&\text{one variable},\\
  6,&\text{two variables sharing no clause},\\
 10,&\text{two variables sharing a clause}.
 \end{cases}
\]

Thus no accepted block exists on F_p, even though F_p is satisfiable. This
refutes the candidate's universal progress claim. It does not rule out
larger blocks, a different size budget, other preprocessing, a direct SAT
witness search, or an equisatisfiable transformation beyond this operation.

### Allowing growth does not remove the known proof-system limitation

The increase by three above does **not** itself prove superpolynomial growth
over subsequent rounds. A polynomial allowance for total growth would bypass
that particular rejection rule on the first round. We therefore separately
check the broader repair of retaining explicit resolution elimination while
changing its budget or block size.

Every nontrivial new clause in an accepted elimination is an ordinary binary
resolvent of two previously available clauses. Keep those parent references
in a derivation log, even after the working formula discards clauses.
Removing a duplicate, tautology or subsumed clause adds no inference. If the
algorithm eventually reports UNSAT because it has derived the empty clause,
the logged ancestors of that clause are an ordinary resolution refutation.
Its number of lines is at most the original clause count plus the total
number of explicitly generated resolvents in the accepted eliminations.
Consequently polynomial total running time for this mechanism on all UNSAT
inputs would supply polynomial-size ordinary resolution refutations for all
of them. Choosing an elimination order adaptively or grouping steps does not
change this simulation. Small working memory alone does not bound the total
number of generated lines.

The known lower bound already used in [robust_ceiling.md](robust_ceiling.md)
rules this out. We checked Ben-Sasson and Wigderson, *Short Proofs Are
Narrow—Resolution Made Simple*, JACM 48(2), 149–169 (2001), in the
[original paper](https://people.inf.ethz.ch/emo/SatSem05/Papers/BensassonWidgerson01.pdf):
Section 2's ordinary DAG resolution definition, Theorem 3.5/Corollary 3.6,
Theorem 4.4 and Corollary 4.5. Odd-charge Tseitin CNFs on connected cubic
expanders with q vertices have initial width three and O(q) variables,
require width Omega(q), and hence require exp(Omega(q)) resolution lines.
With dense binary variable names the input length is L=Theta(q log q), so
this is exp(Omega(L/log L)), still superpolynomial in L.

This is an application of an established lower bound, not a new one. It
stops a complete polynomial SAT proposal whose only UNSAT mechanism is the
explicit resolution elimination just specified, even with a more permissive
budget. A method using Gaussian elimination, extension axioms or a different
semantic decision rule is outside this simulation. In fact parity reasoning
decides these Tseitin contradictions efficiently. No lower bound for general
SAT algorithms follows. The downloaded paper's SHA-256 was
`a47025f36a47da2d39e490bdeaaa39b5618eb9f947cfe609f1833ea1511248f4`.

### Executed checks and scope

The exact elimination operation was independently compared with existential
truth-table evaluation on all 256 two-variable CNFs over the eight nonempty
nontautological clauses, plus three normalization/contradiction controls.
All 1,295 projected assignments agreed. Empty CNFs and empty clauses were
checked explicitly.

For p=11,13,17, we then tested the base formula and two signed/permuted
versions. Known witnesses were checked on the actual transformed clauses.
All 369 single projections and 7,632 unordered pairs agreed with the counts
above; each pair was checked in both orders, for 15,264 ordered projections.
The base-formula pair counts are:

| p | Variables | Clauses | Pairs increasing clauses by 6 | Pairs increasing clauses by 10 |
|---|---:|---:|---:|---:|
| 11 | 33 | 66 | 330 | 198 |
| 13 | 39 | 78 | 507 | 234 |
| 17 | 51 | 102 | 969 | 306 |

Each clause contributes three distinct adjacent pairs, so the last column
equals 18p; the other column is binomial(3p,2)-18p. These finite checks support
the implementation and identities. The all-size conclusions use the proofs
above, not extrapolation of the table. This is not a Lean verification or an
all-algorithm SAT lower bound. After the progress claim failed, no new general
solver or larger benchmark suite was built.

The complete independent audit is reproducible with this Python block:

```python
from itertools import combinations, product
from random import Random


def normalize(clauses):
    clauses = {frozenset(c) for c in clauses}
    clauses = {c for c in clauses if not any(-lit in c for lit in c)}
    return frozenset(c for c in clauses if not any(d < c for d in clauses))


def eliminate(clauses, variable):
    positive = [c - {variable} for c in clauses if variable in c]
    negative = [c - {-variable} for c in clauses if -variable in c]
    rest = [c for c in clauses if variable not in c and -variable not in c]
    return normalize(rest + [a | b for a in positive for b in negative])


def family(p):
    return normalize([
        tuple((1 if t < 3 else -1) * v for v in
              (i + 1, p + (i+t) % p + 1, 2*p + (i+2*t) % p + 1))
        for t in range(6) for i in range(p)
    ])


def holds(clauses, bits):
    return all(any(bits[abs(lit)-1] == (lit > 0) for lit in c) for c in clauses)


universe = ((1,), (-1,), (2,), (-2,), (1, 2), (1, -2), (-1, 2), (-1, -2))
controls = [tuple(c for j, c in enumerate(universe) if mask >> j & 1)
            for mask in range(256)]
controls += [((),), ((1, -1), (2,), (2,)), ((1,), (-1,), (1, 2))]
projection_checks = 0
for source in controls:
    reduced = normalize(source)
    for bits in product((False, True), repeat=2):
        assert holds(source, bits) == holds(reduced, bits)
    for block in ((1,), (2,), (1, 2)):
        projected = reduced
        for variable in block:
            projected = eliminate(projected, variable)
        assert all(abs(lit) not in block for c in projected for lit in c)
        remaining = tuple(v for v in (1, 2) if v not in block)
        for values in product((False, True), repeat=len(remaining)):
            fixed = dict(zip(remaining, values))
            expected = any(holds(source, bits) for bits in product((False, True), repeat=2)
                           if all(bits[v-1] == value for v, value in fixed.items()))
            bits = tuple(fixed.get(v, False) for v in (1, 2))
            assert holds(projected, bits) == expected
            projection_checks += 1
assert normalize(()) == frozenset()
assert normalize(((),)) == frozenset({frozenset()})
print({'small_formulas': len(controls), 'projection_checks': projection_checks})

singles = pairs = 0
for p in (11, 13, 17):
    base = family(p)
    for seed in (None, 0, 1):
        labels = list(range(1, 3*p+1))
        if seed is not None:
            rng = Random(seed)
            rng.shuffle(labels)
            labels = [v if rng.getrandbits(1) else -v for v in labels]
        clauses = normalize(tuple(labels[abs(lit)-1] if lit > 0 else
                                  -labels[abs(lit)-1] for lit in c) for c in base)
        witness = [False] * (3*p)
        for old, label in enumerate(labels):
            witness[abs(label)-1] = (old < p) == (label > 0)
        assert holds(clauses, witness)
        assert len(clauses) == 6*p and all(len(c) == 3 for c in clauses)
        scopes = [frozenset(abs(lit) for lit in c) for c in clauses]
        assert all(len(a & b) <= 1 for a, b in combinations(scopes, 2))
        variables = range(1, 3*p+1)
        assert all(sum(v in c for c in clauses) == 3 and
                   sum(-v in c for c in clauses) == 3 for v in variables)
        one = {v: eliminate(clauses, v) for v in variables}
        for result in one.values():
            assert len(result) - len(clauses) == 3
            assert sum(map(len, result)) - 18*p == 18
            singles += 1
        histogram = {}
        for x, y in combinations(variables, 2):
            result = eliminate(one[x], y)
            assert result == eliminate(one[y], x)
            shared = any(x in scope and y in scope for scope in scopes)
            delta = len(result) - len(clauses)
            assert delta == (10 if shared else 6)
            histogram[delta] = histogram.get(delta, 0) + 1
            pairs += 1
        assert histogram[10] == 18*p
        print({'p': p, 'seed': seed, 'variables': 3*p, 'clauses': 6*p,
               'single_clause_increase': 3, 'pair_clause_increase_counts': histogram})
print({'single_projections': singles, 'unordered_pairs_both_orders': pairs,
       'ordered_pair_projections': 2*pairs, 'all_checks_passed': True})
```

**Decision.** Reject the one- and two-variable nonincreasing-clause strategy
by the explicit SAT family. Also stop a budget-only repair that still relies
solely on explicit ordinary resolution to refute every UNSAT input, by the
known lower bound and the trace simulation. Retain the projection and resource
analysis; do not assume that a suitable block always exists. Other shrinking
methods remain unexamined by these arguments. This investigation supplies no
complete P-versus-NP proof candidate in either direction.

## 13. Alternative mechanisms: holographic algorithms and circuit magnification

**Date:** 2026-11-10 JST. The user asked to find other methods after the
clause-elimination attempt. We examined an exact counting route toward P=NP
and an existing magnification route toward P≠NP. Neither supplies a complete
proof. The literature results below are attributed, not claimed as new work;
this section records the candidate we actually tested and its stopping point.

### 13.1 Candidate: change the basis of a SAT tensor network

A CNF can be represented by a network of equality tensors at variables and
clause truth tensors at clauses. Summing over edge bits gives exactly #SAT.
An invertible matrix T on one end of each edge and T^(-transpose) on the
other preserves this scalar contraction. If we could uniformly turn every
input into a polynomial-size planar weighted perfect-matching instance,
with polynomial construction cost and exactly represented weights of
polynomial bit length, Pfaffian evaluation would give #SAT in FP and hence
P=NP. Rational weights are one concrete setting in which exact arithmetic
and its bit cost can be controlled. An abstract tensor identity alone does
not establish this algorithm.

**Known constraint.** A planar matchgate signature has only even-parity
support or only odd-parity support. Its entries also satisfy the matchgate
identities. These are necessary conditions over the complex numbers;
adding internal vertices or choosing negative weights does not remove them.
See Cai–Gorenstein, *Matchgates Revisited*,
[arXiv:1303.6729v2](https://arxiv.org/pdf/1303.6729v2), Theorems 1–2 and
Section 5. We use their planar boundary-order convention.

Here is a precise candidate that fails: use the **same invertible 2-by-2
matrix on every variable-side edge**, and its inverse transpose on every
clause-side edge, then replace each transformed tensor by a planar matchgate.
It already fails for the two ternary tensors

\[
 E_{abc}=[a=b=c],\qquad O_{abc}=[a\lor b\lor c].
\]

For example, with H=((1,1),(1,-1)), H^(tensor 3) E is 2 on the even
assignments and 0 on the odd ones. However, (H/2)^(tensor 3) O is 7/8
at 000 and -1/8 everywhere else, so it has both parities. The factor 1/2
on the clause side is required to preserve contraction.

**Audit of every common basis, not just H.** Suppose both transformed
tensors had pure parity. Set Z=diag(1,-1) and A=T^(-1) Z T. For signs
epsilon, eta in {1,-1}, this would imply

\[
 A^{\otimes3}E=\epsilon E,\qquad
 (A^{\mathsf T})^{\otimes3}O=\eta O.
\]

Write A=((a,b),(c,-a)). Since A²=I, a²+bc=1. The 001 and 011
components of the first equation give

\[
 a(ac-b^2)=0,\qquad a(c^2+ab)=0.
\]

If a is nonzero and b,c are nonzero, these equations imply bc=-a²,
contradicting a²+bc=1. If either b or c is zero, both are zero; then the
000 and 111 components would require a³=-a³=epsilon, also impossible
over the complex numbers. Thus a=0 and bc=1. But the 000 component of
(A^transpose)^(tensor 3) O is then c³ O_111=c³, which is nonzero,
whereas eta O_000=0. This is a contradiction.

Consequently **no common invertible complex basis makes both of these
tensors planar matchgate signatures under the dual transformation**.
This is an application of the known parity condition. It excludes this
particular local encoding, not distinct bases on different incidences, grouping
several tensors before transformation, other tractable tensor families, or
all holographic algorithms. It also imposes exact counting, which is stronger
than the SAT decision goal.

### 13.2 A separate check: ordinary crossings cannot be copied locally

Even if a different encoding repaired the preceding obstruction, arbitrary
SAT incidence graphs are not planar. With four boundary bits in cyclic
order, an ordinary crossing would need

\[
 X_{abcd}=[a=c][b=d].
\]

Taking alpha=1000 and beta=0111 in the matchgate identity (and multiplying
by -1) requires every such planar signature f to obey

\[
 f_{0000}f_{1111}-f_{1100}f_{0011}
       +f_{1010}f_{0101}-f_{1001}f_{0110}=0.
\]

For X the left side is 2. Thus an exact planar matchgate replacement of
this boundary relation is impossible over characteristic other than 2,
regardless of the size of the replacement. The known **signed** crossover
has entries 1 at 0000,0101,1010 and -1 at 1111; it satisfies the identities
but changes the ordinary counting tensor. This is exactly the gadget in
Cai–Gorenstein, Section 5, equations (43)–(46), not a newly found gadget.

Working modulo 2 removes this particular sign obstruction, but the parity
of #SAT does not decide SAT: (x OR y) AND (x OR NOT y) has two solutions,
whereas an unsatisfiable formula has zero. Both counts vanish modulo 2.
This example alone does not rule out reductions using isolation or multiple
different queries; no deterministic polynomial construction of that kind
was obtained here.

**Decision.** Stop the common-basis/local-planarization candidate. A global
transformation would need a new construction with its own exactness and
total-cost proof. Do not spend a new solver implementation on either of the
invalid local replacements.

### 13.3 A different lower-bound target with the right endpoint

For the next investigation, retain **circuit hardness magnification for
search-MCSP**, rather than the previously stopped memory-only argument.
The input is an explicit N=2^n-bit truth table. Fix s(n)=n². On every table
having a circuit of at most s(n) gates, the search problem must output a
description of such a circuit. A proposed output can be checked against all
N bits in time polynomial in N. Rejecting an invalid output also supplies a
failure flag on a table with no such circuit. No canonical hard table, or
free access to an exponentially long implicit input, is assumed.

The exact sufficient target is:

> There is no family of general Boolean circuits solving search-MCSP[n²]
> with size N·poly(n) and depth poly(n).

Equivalently, for every fixed constant c there are infinitely many n for
which no circuit of size at most N n^c and depth at most n^c solves all
inputs of that length. Finite exceptions and constant factors can be
absorbed by increasing c. Depth here is **polynomial in log N**, not constant
depth or just O(log N). Circuits may reuse intermediate computations and
have many output bits.

McKay–Murray–Williams, *Weak Lower Bounds on Resource-Bounded Compression
Imply Strong Separations of Complexity Classes* (STOC 2019),
[author-hosted paper](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf),
**Theorem 1.4, third bullet**, gives the first implication below; the second
uses P contained in P/poly:

\[
 \text{target}\quad\Longrightarrow\quad
 \mathrm{NP}\not\subseteq\mathrm{P/poly}\quad\Longrightarrow\quad
 \mathrm P\ne\mathrm{NP}.
\]

We specialized their oracle A to a trivial predicate and s(n) to n².
Their proof is by contraposition: assuming NP is contained in P/poly,
polynomial-hierarchy merging queries have polynomial-size circuits.
Replacing the short oracle gates in their construction then gives the
forbidden N·poly(n)-size, poly(n)-depth search circuit. We checked the
statement and this replacement argument in Section 5 of the original paper.
The adjacent **second** bullet, with O(log N) depth, only yields
NP not contained in NC1; that conclusion alone does not resolve P vs NP.

**First filter on techniques.** Their Theorem 1.1 already gives a small
circuit for MCSP with short polynomial-hierarchy oracle gates; the underlying
search construction is in Lemma 3.1. Setting s=n² and ell=s³ gives
N·poly(n) size, poly(n) depth, and oracle arity poly(n), unconditionally.
Thus a proposed lower-bound argument cannot remain valid unchanged when
arbitrary poly(n)-input functions are allowed as unit-cost gates: this
enlarged model already has a circuit within the target budget. The argument
must charge the computation inside those gates. This rejects a method with
that specific invariance, not every lower-bound technique.

This is consistent with the broader locality barrier studied in
Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam,
[*Beyond Natural Proofs: Hardness Magnification and Locality*,
arXiv:1911.08297v1](https://arxiv.org/pdf/1911.08297v1), especially
Sections 1.3 and 5. Its separate frontiers with endpoints NC1, NQP or EXP
must not be substituted for the P-versus-NP endpoint above.

**Remaining core:** prove the stated search-circuit lower bound with a
technique that distinguishes actual gates from these short oracles. We
have not done this, and have no evidence that it is easier than resolving
P vs NP by a different route. Magnification is an established connection,
not a new lower bound or a complete-proof candidate. The earlier streaming
prefix-counting failure remains in force and is not reopened.

### 13.4 Exact finite checks

The reproduction below uses only Python's standard library. It checks all
496 invertible integer matrices with entries in {-2,-1,0,1,2}; both the
preservation of the scalar contraction and failure of simultaneous parity
hold. The unsigned crossing violates 8 of the 256 ordered-pair identities;
the signed crossing violates none. These tests check conventions and
arithmetic. The arbitrary-complex-basis obstruction is the argument in
13.1, not an extrapolation from these matrices. No Lean formalization or
asymptotic circuit lower bound is claimed.

```python
from fractions import Fraction as Q
from itertools import product


def transform(tensor, matrix, arity):
    bits = list(product((0, 1), repeat=arity))
    result = []
    for out in bits:
        value = Q(0)
        for coefficient, source in zip(tensor, bits):
            term = Q(coefficient)
            for i in range(arity):
                term *= matrix[out[i]][source[i]]
            value += term
        result.append(value)
    return result


def dual(matrix):
    (a, b), (c, d) = matrix
    det = a * d - b * c
    return ((Q(d, det), Q(-c, det)), (Q(-b, det), Q(a, det)))


def has_parity(tensor):
    return len({i.bit_count() % 2 for i, value in enumerate(tensor) if value}) <= 1


def mgi_violations(tensor, arity):
    bad = 0
    for alpha, beta in product(range(1 << arity), repeat=2):
        differing = [1 << (arity - 1 - i) for i in range(arity)
                     if (alpha ^ beta) & (1 << (arity - 1 - i))]
        residual = sum((-1) ** (i + 1) * tensor[alpha ^ bit] * tensor[beta ^ bit]
                       for i, bit in enumerate(differing))
        bad += residual != 0
    return bad


equality = [1, 0, 0, 0, 0, 0, 0, 1]
clause_or = [0, 1, 1, 1, 1, 1, 1, 1]
hadamard = ((1, 1), (1, -1))
assert transform(equality, hadamard, 3) == [2, 0, 0, 2, 0, 2, 2, 0]
assert transform(clause_or, dual(hadamard), 3) == [Q(7, 8)] + [Q(-1, 8)] * 7

checked = 0
for a, b, c, d in product(range(-2, 3), repeat=4):
    if a * d == b * c:
        continue
    matrix = ((a, b), (c, d))
    left = transform(equality, matrix, 3)
    right = transform(clause_or, dual(matrix), 3)
    # Independent semantic check: the scalar network contraction stays 1.
    assert sum(x * y for x, y in zip(left, right)) == 1
    assert not (has_parity(left) and has_parity(right))
    checked += 1

crossing = [int(a == c and b == d) for a, b, c, d in product((0, 1), repeat=4)]
signed = crossing.copy()
signed[15] = -1
assert crossing[0] * crossing[15] - crossing[12] * crossing[3] + crossing[10] * crossing[5] - crossing[9] * crossing[6] == 2
violations = mgi_violations(crossing, 4)
assert violations > 0
assert mgi_violations(signed, 4) == 0

sat_count = sum((x or y) and (x or not y) for x, y in product((0, 1), repeat=2))
unsat_count = sum(x and not x for x in (0, 1))
assert sat_count == 2 and unsat_count == 0 and sat_count % 2 == unsat_count % 2
print(f'invertible integer bases: {checked}; contraction and parity checks passed')
print(f'unsigned crossing MGI violations: {violations}/256; signed crossing: 0/256')
print('Hadamard dual factors and SAT parity counterexample: passed')
```

## 14. Continuing the circuit target: essential inputs and sparse reconstruction

**Date:** 2026-11-10 JST. We continued the search-MCSP[n²] circuit target
from 13.3. The first attempted lower bound charges the need to distinguish
many nearby truth tables and to choose different circuit descriptions.
The dependence argument yields only a linear size bound. Explicit shared
circuits show why the proposed sparse-input strengthening does not supply
the missing bound. These are elementary applications of circuit counting
and sorting networks, not a new general circuit lower bound.

Throughout, N=2^n is the **explicit** truth-table input length, n>=2,
and the counted basis is binary AND/OR and unary NOT. Constants, input
wires and fanout are free. A search output is a standard fixed-length,
padded circuit description with a status bit. Its length r is
O(n² log n), since the permitted output circuit has at most n² gates.
This description is distinct from the much larger circuit performing the
search on N input bits.

### 14.1 What full input dependence actually proves

Consider the zero table and the N tables with a single 1. Every one has a
size-n² circuit: a point indicator needs at most n NOT gates and n-1 AND
gates. The search output for zero cannot equal its output for any of these
point tables, since one described circuit cannot compute two different
functions. Thus every truth-table input bit affects the output vector.

This proves that a deterministic query algorithm must read all N bits on
the zero table. For a general fan-in-two circuit with G gates, r output
bits and depth d, however, it only gives

\[
 G\ge N-r,\qquad r\,2^d\ge N.
\]

For the first inequality, keep the ancestors of the outputs. All N inputs
are present. Ignoring constants, the undirected graph has N+G vertices,
at most 2G edges and at most r connected components: every component
contains an output. Hence 2G>=N+G-r. The same reasoning applies if the
original circuit had additional unused gates. For the second inequality,
each output cone of depth d has at most 2^d input leaves. Overlap among
these cones can only reduce their union.

With r=poly(n), this yields G>=N-poly(n) and
d>=n-O(log n). Both are compatible with size N·poly(n) and depth poly(n).
Multiplying an input-dependence bound separately by the number of output
bits would charge shared computations repeatedly.

**Explicit check of that failure.** For tables promised to contain at
most one 1, a balanced binary tree returns an active flag and the address
of the 1 (address zero when inactive). At a node covering 2^h positions,
OR the two active flags, take the right active flag as the high address
bit, and OR each corresponding pair of the remaining h-1 address bits.
Inactive children have zero address bits. The singleton promise ensures
that no two active addresses are combined.

The construction uses exactly

\[
 \sum_{h=1}^n h\,\frac{N}{2^h}=2N-n-2
\]

OR gates and depth at most n. Its output distinguishes zero from every
one-bit perturbation; each address bit depends on N/2 different inputs.
Yet the intermediate computations are shared, and the total size is
linear in N. Formatting a point-indicator circuit from the address and
active bit costs only poly(n), so it does not change this asymptotic
conclusion. On tables outside the promise this is not an MCSP solver.

### 14.2 Strengthening to many ones still permits small search circuits

Set k=floor(n/2). For every table with at most k ones, we construct its
small circuit using a search circuit of size O(N n³), depth O(n²),
and a polynomial-time uniform construction in its explicit size.

Make a record (T_i,i) for each input bit, with an n-bit address. A standard
bitonic sorting network sorts the one-bit keys in descending order while
carrying the addresses. It uses N n(n+1)/4 comparators in n(n+1)/2 layers.
The first k records then contain all active addresses, padded with inactive
records. The key of record k+1 reports overflow. **Overflow means that the
sparsity promise failed, not that the table has no small circuit.** For
example, the all-one table overflows but has a zero-gate constant circuit.

No unit-cost operation on a long record is assumed. To compare two records,
use two gates to compute whether they must swap and one to negate that
control. Each pair of record bits takes two three-gate multiplexers.
With n+1 bits per record this is 6n+9 gates per comparator and depth at
most 5. Thus the extractor has the explicit bounds

\[
 G_{\rm extract}\le(6n+9)\frac{Nn(n+1)}4,\qquad
 d_{\rm extract}\le\frac{5n(n+1)}2.
\]

The sorting construction is standard: sort the two halves in opposite
directions, then merge a bitonic sequence recursively. For binary keys,
the ones of a bitonic sequence form a cyclic interval. Comparing opposite
positions leaves the lower half all zero if there are at most half ones,
or the upper half all one otherwise; the residual half remains bitonic.
Induction gives the merge and the layer count. Every compare-exchange
preserves its two records, including when their keys are equal.

From the first k records (a_j, p_j), output the description of

\[
 D_T(x)=\bigvee_{j=1}^k
       \left(a_j\land\bigwedge_{i=1}^n[x_i=(p_j)_i]\right).
\]

In this output circuit, a_j and the address bits are **constants chosen
by the extractor**, not extra inputs to the function being represented.
Share the n negated input wires. Each term uses n-1 AND gates for its
literals and one AND with its active constant. Joining the terms uses
k-1 OR gates. Including inactive slots, its gate count is exactly

\[
 h(n,k)=n+kn+k-1\le n².
\]

The description formatter is also cheap: the wiring template is fixed;
each literal source field selects between the known indices of x_i and
NOT x_i using one extracted address bit. Each bit of such a field is a
constant, that selection bit, or its negation. The active constant is
encoded similarly. This needs O(kn) extra gates and at most one extra
layer, not an oracle for circuit synthesis. All bounds above therefore
remain O(N n³) size and O(n²) depth after formatting. A direct generator
writes the network and template in time polynomial in N and n.

There are already at least binomial(N,k)>=(N/k)^k=2^(Omega(n²)) distinct
tables in this promise for growing n. Nevertheless this entire family has
the preceding small search circuit. Counting its distinct answers or
forcing changes of the represented function cannot by itself yield the
target lower bound. This does not give a small compressor for arbitrary
YES instances of MCSP.

### 14.3 The same countercheck around a given dense function

This is not limited to functions that themselves have few ones. Let B be
a **given** circuit of size b<=floor(n²/4), let n>=4, and put
k=floor(n/4). Consider tables differing from B's table on at most k bits.
Generate B's table in O(N·poly(n)) time by evaluating the supplied circuit;
this explicitly pays for all N entries. Feed T XOR tt(B) into the sparse
extractor, then output B XOR D, sharing the two output subcircuits. XOR
requires four AND/OR/NOT gates. The resulting circuit has at most

\[
 b+h(n,k)+4
 \le \frac{n²}{2}+\frac{5n}{4}+3
 \le n²
\]

gates. The first stage only complements those table-input bits where the
known B is 1, costing at most N extra NOT gates. It still has
N·poly(n) size and poly(n) depth. The circuit description of B is included
in the output; it is not replaced by an uncharged semantic oracle.

This is a construction given B, not a method for finding B from an
arbitrary table. Choosing an unknown useful center cannot be assumed free.
The example excludes a proposed lower bound based only on many small
perturbations of an available model, including dense models.

### 14.4 Decision and reproducible checks

Stop the attempted amplification from essential inputs, many sparse tables,
or small perturbations of a known circuit. The proven general lower bound
here is only linear; the explicit promise compressors fit the budget that
the magnification target must exclude. No superlinear general lower bound,
new magnification theorem, Lean proof, or P-versus-NP resolution is claimed.
The broad circuit-magnification target from 13.3 remains open. Any next
argument must address arbitrary size-n² circuit functions without assuming
their representation, their center, or their sparse exception set is known.

The standalone check below constructs actual fan-in-two gate DAGs. It
verifies 515 zero/singleton cases and checks the sorting construction on
68,674 tables, including **every truth table on 2, 3 and 4 variables**.
For 5 and 6 variables it includes every support of size at most two and
fixed-seed additional cases. A separate oracle checks that output addresses
are a permutation, carry their original bits, and are ordered by key.
For 2,889 in-promise cases it builds the output circuit and evaluates it
on every original input using a scalar evaluator, rather than the packed
evaluator used for the extractor. Another 345 output circuits check the
dense-center extension. These tests validate the construction and exact
gate counts; the all-size bounds are the arguments above.

```python
from itertools import combinations
from random import Random


class DAG:
    def __init__(self, inputs):
        self.inputs, self.gates = inputs, []
        self.depth = [0] * (inputs + 2)

    def gate(self, op, *args):
        assert len(args) == (1 if op == 'NOT' else 2)
        assert all(0 <= a < len(self.depth) for a in args)
        self.gates.append((op, args))
        self.depth.append(1 + max(self.depth[a] for a in args))
        return len(self.depth) - 1

    def packed(self, cases):
        width = (len(cases) + 7) // 8
        columns = [bytearray(width) for _ in range(self.inputs)]
        for j, case in enumerate(cases):
            for i in range(self.inputs):
                if case >> i & 1:
                    columns[i][j // 8] |= 1 << (j % 8)
        mask = (1 << len(cases)) - 1
        values = [0, mask] + [int.from_bytes(c, 'little') for c in columns]
        for op, args in self.gates:
            a = values[args[0]]
            values.append(mask ^ a if op == 'NOT' else
                          a & values[args[1]] if op == 'AND' else a | values[args[1]])
        return values


def singleton_encoder(n):
    dag = DAG(1 << n)
    def tree(lo, h):
        if h == 0:
            return lo + 2, []
        lf, la = tree(lo, h - 1)
        rf, ra = tree(lo + (1 << (h - 1)), h - 1)
        return dag.gate('OR', lf, rf), [rf] + [dag.gate('OR', a, b) for a, b in zip(la, ra)]
    flag, address = tree(0, n)
    return dag, [flag] + address


def sparse_encoder(n):
    count = 1 << n
    dag = DAG(count)
    records = [[i + 2] + [(i >> j) & 1 for j in range(n - 1, -1, -1)]
               for i in range(count)]
    block = 2
    while block <= count:
        stride = block // 2
        while stride:
            for i in range(count):
                j = i ^ stride
                if j <= i:
                    continue
                a, b = records[i], records[j]
                high_first = (i & block) == 0
                u, v = (a[0], b[0]) if high_first else (b[0], a[0])
                swap = dag.gate('AND', dag.gate('NOT', u), v)
                keep = dag.gate('NOT', swap)
                left, right = [], []
                for x, y in zip(a, b):
                    left.append(dag.gate('OR', dag.gate('AND', x, keep), dag.gate('AND', y, swap)))
                    right.append(dag.gate('OR', dag.gate('AND', y, keep), dag.gate('AND', x, swap)))
                records[i], records[j] = left, right
            stride //= 2
        block *= 2
    return dag, records


def witness(n, records):
    dag = DAG(n)
    negated = [dag.gate('NOT', i + 2) for i in range(n)]
    terms = []
    for active, *address in records:
        literals = [i + 2 if bit else negated[i] for i, bit in enumerate(address)]
        term = literals[0]
        for literal in literals[1:]:
            term = dag.gate('AND', term, literal)
        terms.append(dag.gate('AND', term, active))  # constants 0 and 1
    result = terms[0]
    for term in terms[1:]:
        result = dag.gate('OR', result, term)
    return dag, result


def scalar_table(dag, output):
    table = 0
    for x in range(1 << dag.inputs):
        values = [False, True] + [bool(x >> (dag.inputs - 1 - j) & 1) for j in range(dag.inputs)]
        for op, args in dag.gates:
            a = values[args[0]]
            values.append(not a if op == 'NOT' else
                          a and values[args[1]] if op == 'AND' else a or values[args[1]])
        table |= int(values[output]) << x
    return table


def xor_gate(dag, a, b):
    union = dag.gate('OR', a, b)
    intersection = dag.gate('AND', a, b)
    return dag.gate('AND', union, dag.gate('NOT', intersection))


single_cases = 0
for n in range(2, 9):
    count = 1 << n
    dag, outputs = singleton_encoder(n)
    cases = [0] + [1 << i for i in range(count)]
    values = dag.packed(cases)
    assert len(dag.gates) == 2 * count - n - 2
    assert max(dag.depth[o] for o in outputs) <= n
    for j, case in enumerate(cases):
        bits = [(values[o] >> j) & 1 for o in outputs]
        address = sum(b << (n - 1 - i) for i, b in enumerate(bits[1:]))
        assert bits[0] == bool(case)
        assert not case or address == case.bit_length() - 1
    single_cases += len(cases)

sort_cases = reconstructed = dense_reconstructed = 0
for n in range(2, 7):
    count, k = 1 << n, n // 2
    if n <= 4:
        cases = list(range(1 << count))
    else:
        cases = [sum(1 << i for i in support)
                 for r in range(3) for support in combinations(range(count), r)]
        rng = Random(1700 + n)
        cases += [sum(1 << i for i in rng.sample(range(count), k)) for _ in range(128)]
        cases += [rng.getrandbits(count) for _ in range(64)]
        cases = sorted(set(cases))
    dag, records = sparse_encoder(n)
    values = dag.packed(cases)
    mask = (1 << len(cases)) - 1
    comparisons = count * n * (n + 1) // 4
    assert len(dag.gates) == (6 * n + 9) * comparisons
    assert max(dag.depth[o] for record in records for o in record) <= 5 * n * (n + 1) // 2
    packed = [[values[o] for o in record] for record in records]
    for a, b in zip(packed, packed[1:]):
        assert (mask ^ a[0]) & b[0] == 0
    # Independent oracle: each address occurs exactly once, with its original bit.
    for address in range(count):
        seen = 0
        for key, *bits in packed:
            hit = mask
            for j, bit in enumerate(bits):
                hit &= bit if address >> (n - 1 - j) & 1 else mask ^ bit
            assert seen & hit == 0
            assert (key ^ values[address + 2]) & hit == 0
            seen |= hit
        assert seen == mask
    for j, case in enumerate(cases):
        overflow = (packed[k][0] >> j) & 1
        assert overflow == (case.bit_count() > k)
        if overflow:
            continue
        decoded = [[(v >> j) & 1 for v in record] for record in packed[:k]]
        small, output = witness(n, decoded)
        assert len(small.gates) == n + k * n + k - 1 <= n * n
        assert scalar_table(small, output) == case
        reconstructed += 1
        if n >= 4 and case.bit_count() <= n // 4:
            for center in ('input', 'and', 'xor'):
                small, output = witness(n, decoded[:n // 4])
                if center == 'input':
                    base, r = 2, 0
                elif center == 'and':
                    base, r = small.gate('AND', 2, 3), 1
                else:
                    base, r = xor_gate(small, 2, 3), 4
                corrected = xor_gate(small, base, output)
                assert r <= n * n // 4 and len(small.gates) <= n * n
                base_table = sum(int((x >> (n - 1) & 1) if center == 'input' else
                                     ((x >> (n - 1) & 1) & (x >> (n - 2) & 1)) if center == 'and' else
                                     ((x >> (n - 1) & 1) ^ (x >> (n - 2) & 1))) << x
                                 for x in range(count))
                assert scalar_table(small, corrected) == case ^ base_table
                dense_reconstructed += 1
    sort_cases += len(cases)
    print({'n': n, 'cases': len(cases), 'encoder_gates': len(dag.gates),
           'encoder_depth': max(dag.depth[o] for rec in records for o in rec)})

print({'singleton_cases': single_cases, 'sorting_cases': sort_cases,
       'reconstructed_circuits': reconstructed,
       'dense_reconstructed_circuits': dense_reconstructed, 'all_checks_passed': True})
```

## Reporting a possible resolution

Flag a provisional candidate before final verification when there is a concrete all-input algorithm and a substantive argument that every stage has fixed polynomial bit cost, or a concrete lower-bound argument covering every deterministic polynomial-time decider for a language in NP. Identify the central lemma, what is checked, what is still open, and the likeliest counterexample. A conditional statement that merely restates the missing P versus NP claim, passing finite tests, faster performance on a family, a restricted representation lower bound, or a successful ETH endpoint rebuild alone does not trigger this label.
