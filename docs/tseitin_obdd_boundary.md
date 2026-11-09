# Phase 27 preregistration: ordered DAGs versus exact Tseitin affine covers

Date: 2026-11-08 JST. Starting main: `5a37d5b6eb7467d40355e4734660d46300d53c00`; previous completed PR #4. No open PRs, no newer main workflow changes at the start.

## Falsifiable hypotheses and independent gates (registered before coding)

The phase-26 relation `T_m` is the satisfying assignment set of its explicit AND/XOR Tseitin 3-CNF, with (4m-1) Boolean variables, (7m-3) clauses, and exact affine one-cover number (2^m-1).

- **H1, negative transfer gate.** Contrary to a naive proposed size lower bound (\text{OBDD nodes}\ge c_{\rm aff}(T_m)), this same relation admits a deterministic ordered read-once decision DAG with variable order `x0,y0,p0,x1,y1,p1,t1,...`, no more than **four live states per variable level**, and no more than `12m-7` nonterminal nodes (two shared terminals excluded), for every (m\ge1). Every accepted assignment must satisfy the *entire* Tseitin CNF, not just its projection.
- **H2, order-sensitivity gate.** Under any OBDD that tests all `x` variables before any of the other variables, the cut just after the `x` block has at least (2^m-1) nonreject residual states. This lower bound must apply to the same `T_m`.
- **Falsifiers.** A CNF/OBDD mismatch on a complete assignment; an incorrect width/node count; a pair of distinct nonzero `x` prefixes with identical residual Boolean functions; or a missing gate/output constraint in the read-once construction.

**Hard stop and resource budget.** Enumerate full extended Boolean inputs only for `m=1,2,3`, as in phase 26 (maximum (2^{11}=2048) assignments). Enumerate residual suffix truth vectors at these same sizes only. Do not increase the affine-flat RREF/enumeration cap, run SAT solvers on larger examples, or rerun the expensive upstream ETH Lean build. Require a mathematical induction and distinguish it from Python's finite checks. Use standard-library Python, test the gate graph against an independent raw-CNF evaluator, compare accepted-path counts by DAG dynamic programming against an independent exact expected count. Run the existing GitHub research-check and ordinary-PC gates. Abort/generalize neither H1 nor H2 if a small counterexample appears; record it instead.

**Prior art and scope.** Ordered BDDs and sharing of residual functions are classical, not a new complexity model: R. E. Bryant, *Graph-Based Algorithms for Boolean Function Manipulation*, IEEE Trans. Comput. C-35 (1986), 677–691, https://doi.org/10.1109/TC.1986.1676819 ; A. Darwiche and P. Marquis, *A Knowledge Compilation Map*, JAIR 17 (2002), 229–264, https://doi.org/10.1613/JAIR.989 . The `T_m`-specific order contrast and fixed finite audit here are elementary deductions, with no novelty/priority claim.

This is a model-boundary experiment: a compact OBDD for a satisfiable explicit family does not decide arbitrary SAT and neither H1 nor H2 would establish P=NP or P≠NP.

## Outcome: both preregistered gates passed (mathematical proof + bounded audit)

### Theorem 1: a linear-size interleaved OBDD for the **entire** witness CNF

For the exact phase-26 satisfying relation \(T_m\), set the variable order

\[
x_0,y_0,p_0,\quad x_1,y_1,p_1,t_1,\quad\ldots,\quad
x_{m-1},y_{m-1},p_{m-1},t_{m-1}.
\]

Use two shared terminals, *reject* and *accept*. The state at the start of
block \(i\) stores the already validated prefix parity
\(q=\bigoplus_{j<i}p_j\). Reading \(x_i\) temporarily stores \((q,x_i)\);
reading \(y_i\) replaces it with \((q,a_i)\), where \(a_i=x_i y_i\).
Reading \(p_i\) rejects unless \(p_i=a_i\); on success update
\(q\leftarrow q\oplus a_i\). If \(i>0\), reading \(t_i\) rejects unless
\(t_i=q\). For \(m=1\), the output requirement is \(p_0=1\);
otherwise, after the final \(t_{m-1}\) require \(q=1\).

**Correctness proof.** Induct on the pair index \(i\). On every surviving
path, all previous AND and prefix-XOR gate equations hold, and the stored
\(q\) equals their actual prefix parity. The local steps validate the
new AND equation, then the new XOR equation without ever forgetting
a necessary prior bit. Conversely, any assignment satisfying the gate
equations passes all local tests. The final parity test is exactly the
output-unit clause. Hence the accepted full assignments are *precisely*
\(T_m\), with no existential projection shortcut. Every variable appears
once in the common order, so this is an ordered read-once branching program
(OBDD), not merely a general circuit.

Before the first three variables, the numbers of reachable live states
are respectively \(1,2,2\). Each later four-variable block has
\(2,4,4,2\) live states. The two parity values remain reachable before
each later block: choose earlier pair values to fix either parity, then
independently choose the next \(x_i\) and \(a_i\). Thus the explicit
unreduced DAG has **exactly**

\[
\boxed{\text{nonterminal nodes}=5+12(m-1)=12m-7,\qquad
\text{maximum live width}\le4.}
\]

There are two shared terminals and at most \(24m-14\) outgoing
decision arcs. An explicitly layered version carrying a reject sink has
width at most five. The DAG and its variable labels are constructible
uniformly using \(O(m)\) word operations and \(O(m\log m)\) encoded bit
length. Reducing the OBDD can only *decrease* node count. QED.

The earlier theorem \(c_{\mathrm{aff}}(T_m)=2^m-1\) still holds.
For example, at \(m=7\), the minimum affine one-cover is **127**,
whereas the exhibited OBDD has **77** decision nodes and two terminals.
For all \(m\ge7\), the exponential cover number strictly exceeds even
the displayed *total* OBDD node count \(12m-5\).
This refutes any universal lower bound of the proposed form
\(\mathrm{OBDD\ size}\ge c_{\mathrm{aff}}(S)\), even for these small-arity
3-CNF relations with genuine auxiliary gate equations. It does **not**
refute lower bounds for particular proof systems or for different
variable orders.

### Theorem 2: an x-first order has an exponential residual frontier

Consider any deterministic OBDD for the **same** full relation \(T_m\)
whose variable order puts *all* \(x_0,\ldots,x_{m-1}\) first. Immediately
after this prefix, each choice \(x\) induces a Boolean residual
\(R_x\) on the remaining \(y,p,t\) variables. For \(x=0\) it is
identically false. For nonzero \(x\), choose \(y\) with
\(x\cdot y=1\), then use the unique legal gate extension; hence
\(R_x\) is nonzero.

For distinct nonzero \(x,x'\), the two vectors are linearly independent
over \(\mathbb F_2\). Consequently there exists \(y\) solving
\(x\cdot y=1\) and \(x'\cdot y=0\). Give \(p,t\) the unique gate values
for \((x,y)\). This suffix satisfies \(R_x\) and fails \(R_{x'}\),
because the latter projects to the negative inner-product level.
Therefore **all** \(2^m-1\) nonzero residual functions are pairwise
distinct. A deterministic residual-state OBDD cannot merge two of them,
giving

\[
\boxed{\text{live states just after the x block}\ \ge 2^m-1.}
\]

This does not constrain OBDDs with an interleaved variable order:
Theorem 1 shows that such a bound would be false. QED.

### Independent experiment and falsification results

Reproduction (standard library, no solver):

~~~bash
python experiments/tseitin_obdd_boundary.py
python -m unittest discover -s tests -p test_tseitin_obdd_boundary.py -v
python scripts/reproduce.py --out-dir reproduced --check
~~~

The [experiment](../experiments/tseitin_obdd_boundary.py) uses a forward
reachable-state construction and a shared-node dynamic program to count
accepted assignments. The [seven independent tests](../tests/test_tseitin_obdd_boundary.py)
compare **every** full encoded assignment with the original raw 3-CNF
clause evaluator, flip each gate bit of every accepted assignment to
challenge the gate check, count paths separately, and build full
*x-first* suffix truth signatures from the CNF alone.
The deterministic [report](../results/tseitin_obdd_boundary.json) records:

| \(m\) | full encoded assignments checked | OBDD live width | decision nodes | accepted assignments | distinct nonempty x-first residuals |
|---:|---:|---:|---:|---:|---:|
| 1 | 8 | 2 | 5 | 1 | 1 |
| 2 | 128 | 4 | 17 | 6 | 3 |
| 3 | 2048 | 4 | 29 | 28 | 7 |

This does not constitute an exhaustive proof for arbitrary \(m\);
the general claims follow from the separate mathematical inductions
above. Python tests, GitHub CI execution, mathematical proof, and
Lean formalization are distinct evidence levels. **No new Lean theorem
is claimed**. The existing Lean audit only verifies the previously
formalized modules; it does not check Theorems 1–2 here.


**Harness correction (documented failure mode).** The first standalone
experiment entry point printed the JSON but did not accept the existing
reproduction driver's required `--out-dir` argument. The final entry
point accepts that argument and writes an exact deterministic JSON file;
no mathematical assertion or finite search budget was changed.

### What is ruled out, and next falsifier

**Ruled out:** the proposed inference from the minimum exact affine
one-cover size of a SAT witness relation to the number of states or
nodes of an arbitrary, freely shared, deterministically ordered
decision DAG. Sharing and interleaving nonlinear gate variables are
enough to invalidate it.

**Not ruled out:** lower bounds on explicitly restricted inference
models that charge shared subderivations or respect a forced variable
order; potentially hard unsatisfiable families; general SAT algorithms.
The full CNF here is constructively SAT, and even an OBDD of small size
for this particular CNF does not supply a polynomial-time algorithm
on all input CNFs.

**Next adversarial gate:** fix one *concrete* restricted proof/DAG
model and propose a sound transformation from its accepting or
refuting computations into affine flats, with an explicit accounting
for shared nodes and input/output extensions. First run that proposed
charging rule on this \`T_m\` OBDD. Reject it if it still predicts an
exponential number of nodes. Do not simply increase a finite
enumeration cap or call a representation lower bound a time lower
bound. The eventual all-input P versus NP quantifier remains open.

