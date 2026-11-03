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

For the current all-cell search, a general polynomial bound is already ruled
out: exactly-one CNF on `k` variables together with even XOR parity has
`d=r=k-1`, is UNSAT, and forces exactly `2^(k-1)` cell visits in unbudgeted
**decision mode** as well as in exhaustive mode. The input has polynomial
encoded size `O(k^2 log k)`, so this is a superpolynomial worst-case lower bound
for this implementation. The [all-size argument](reverse_engineering.md) does
not lower-bound other SAT algorithms; the family's contradiction itself is
easy to recognize. Improving finite performance or formally proving this
same enumerator correct cannot remove its known worst-case enumeration.

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
