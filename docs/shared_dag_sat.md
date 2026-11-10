# Phase 28: shared-circuit SAT, and a decision-mode counterexample

The goal remains a complete proof of P=NP or P≠NP. This investigation tries
the P=NP direction: keep the nonlinear circuit shared, restrict variables,
normalize the remaining DAG, and reuse answers for identical residuals.
The implementation decides finite inputs when resources suffice. **Its
proposed polynomial state bound fails. No P-versus-NP proof was obtained.**

The operations are familiar Boolean cofactoring, structural hashing and
algebraic rewriting. This is an implemented candidate and an audit of its
limits, not a claim of a novel SAT algorithm or an all-algorithm lower bound.
It does not rely on phase 27's polynomial expansion for the actual search.

## Algorithm and exact scope

[`shared_dag_sat.py`](../src/pnp_lab/shared_dag_sat.py) accepts either an
AND/XOR/NOT circuit with a required output, or a CNF. Constants are 0 and 1;
complemented edges encode NOT without duplicating their operand. Structural
hashing reuses nodes with the same operation and sorted operands. Rules:

1. Flatten positive AND nodes, eliminate constants, remove duplicate
   factors, and reduce a factor together with its complement to zero.
2. Flatten XOR nodes, track complemented edges as a constant parity bit,
   and cancel repeated operands modulo two.
3. In an XOR, factor out the intersection of the factors of **all** its
   terms. An operand other than an AND is a singleton factor. Repeat
   normalization on the residual expression without distributive expansion.
4. Express OR by De Morgan's law. Memoize decision results by residual root.

These are syntactic rules. Different but equivalent Boolean expressions
can have different root IDs; even regrouping a construction can expose a
different factoring opportunity. The routine does not compute a canonical
representation of Boolean functions, try every subset of XOR terms, learn
general clauses, or use an equivalence oracle.

The search chooses the first variable still present in a supplied order
(ascending original input labels by default), tries False then True, and
memoizes both SAT and UNSAT results. SAT stops at its first witness. UNSAT
requires both children to be UNSAT. Cofactoring rebuilds only reachable
nodes containing the selected variable. Search, cofactoring and factoring
use explicit iteration rather than Python call-stack recursion.

### Correctness argument

Each rewrite is an identity of Boolean functions: AND is associative and
idempotent, XOR is addition in F2, NOT is addition of 1, and multiplication
distributes over addition. Taking common factors is a factoring operation,
not an assumption about independent variables. Structural hashing only
identifies exactly equal syntax. Topological induction on circuit nodes
therefore establishes the semantics of construction and each cofactor.

For a residual function f and a variable x, f is satisfiable exactly when
at least one of f[x=0], f[x=1] is satisfiable. The selected variable is
removed in both cofactors, and no rule introduces a new variable. Induction
on the number of remaining variables proves soundness, completeness and
termination of the unbounded mathematical procedure. Memoization preserves
this argument because a reused root has the same function. A cached SAT
assignment concerns only variables in that residual; the traversed branch
values are added on return. Unused original inputs can be set to False.

The finite implementation checks every returned SAT witness against the
original circuit or clauses. An exhausted explicit budget returns `UNKNOWN`,
never UNSAT. The general Python algorithm and this correctness argument
are **not Lean-formalized**. General UNSAT answers do not include a separately
checkable resolution certificate. Finite testing is not a proof of the
absence of implementation bugs.

## A linear-size UNSAT family

For k >= 2 use original inputs, in default order,

\[
 a_1,\ldots,a_k,u,v,b_1,\ldots,b_k.
\]

Write M_i = a_i b_i, T = XOR_i M_i and s = u XOR v. The circuit output is

\[
 H_k = sT\;\mathbin\oplus\;
       \bigoplus_{i=1}^k (uM_i\mathbin\oplus vM_i).
\]

All multiplication denotes AND. Distributivity in F2 proves H_k = 0 on
every assignment, so requiring output 1 is UNSAT for every k. The generator
shares the M_i, computes T by a binary XOR chain, and constructs the right
chain in the sequence uM_1, vM_1, uM_2, vM_2, ..., uM_k, vM_k.
There are exactly **2k+2 inputs and 6k+1 binary gates**. Encoding wire
indices in binary takes O(k log k) bits. This proof of UNSAT is independent
of the new solver.

### Exponential number of states in actual decision mode

**Proposition.** On these circuits, with the stated default variable order
and normalization rules and with budgets disabled or sufficient for
completion, `solve_circuit` expands at least 2^(k-2) distinct nonterminal
states. This is a paper proof for this specific procedure.

**Proof.** Fix 0 <= t <= k-2 and a prefix assignment to a_1,...,a_t. Let S
be the subset assigned True. In the left product the normalized T becomes

\[
 T_{S,t} = \bigoplus_{i\in S} b_i
          \;\mathbin\oplus\;
          \bigoplus_{i=t+1}^k a_i b_i.
\]

At least two of these distinct monomials remain. No two monomials share a
factor, so this is a positive XOR node, not a constant or an AND. The left
product remains an AND of two distinct XOR nodes: s and T_{S,t}.

For precision, the right chain does not remain entirely unfactored. Let
j be its first surviving monomial. The first pair uM_j, vM_j factors to
sM_j. Each subsequent surviving monomial contributes uM_i and vM_i.
Once two distinct monomials survive, their variable supports are disjoint,
so the intersection across all right-chain terms is empty. This describes
the right chain by induction through its prescribed construction; it also
holds after cofactoring. All these right-side terms have at most one XOR
factor, namely s in sM_j. The other factors are original variables.

Consequently the root XOR has a **unique term with two XOR factors**,
sT_{S,t}. It cannot cancel with a right-side term. No common factor belongs
to all root terms: besides sM_j, at least one later monomial contributes a
term with u and another with v, neither having s or T_{S,t} as a factor.
Thus this root is nonconstant. Its distinguished term determines T_{S,t},
which determines S from the occurrences of the singleton b_i terms for
i <= t. Distinct S therefore give distinct structural roots. The root
still mentions every unassigned a_i through T_{S,t}.

Every residual is semantically UNSAT, so the search cannot terminate with
a SAT witness. It must take both branches, and before level k-2 neither
constant simplification nor the memo table merges these distinct prefixes.
In the fixed order it visits all 2^(k-2) prefixes at level k-2 and expands
each on a_(k-1). This proves the bound. Since the encoding length is
O(k log k), the state count is superpolynomial in that length. QED.

This counts states visited by **UNSAT decision**, not the size of a truth
table, a full BDD constructed when decision could stop earlier, or the
number of satisfying assignments. The proposition is about the circuit
interface. It does not transfer the same state count to `solve_cnf` on a
Tseitin encoding; that interface builds a different initial DAG.

### Two controls expose the precise limitation

If u and v are ordered first, u=0 reduces the full output to zero by
common-factor extraction and XOR cancellation. Under u=1, splitting v
reduces both children to zero. At most two nonterminal states suffice,
regardless of k. The experiment observes exactly two for every tested
k >= 2. This is the same circuit and normalizer with a different order.

The one-selector identity uT XOR XOR_i uM_i collapses during construction,
without any search. It checks that factoring really is performed; the
negative result does not depend on disabling all algebraic simplification.

The original circuit is small, every prefix function is identically zero,
and a better order solves the family immediately. Hence there is no bound
here on all variable orders, all rewriting algorithms, general circuits,
or all SAT solvers. Recognizing this family or choosing u and v first does
not establish a polynomial bound on other inputs.

## Executed checks

The deterministic [report](../results/shared_dag_sat.json) records:

| k | Binary gates | Default-order states | Selector-first states | Distinct states at level k-2 |
|---:|---:|---:|---:|---:|
| 2 | 13 | 4 | 2 | 1 |
| 4 | 25 | 36 | 2 | 4 |
| 6 | 37 | 176 | 2 | 16 |
| 8 | 49 | 748 | 2 | 64 |
| 10 | 61 | 3,048 | 2 | 256 |
| 12 | 73 | 12,260 | 2 | 1,024 |

All six outputs are also independently expanded as squarefree F2
polynomials by phase 27's implementation and found to be zero. The report
enumerates every original assignment for k=2 and k=4; it records zero
enumerated assignments at larger k rather than implying those were tested.
The displayed state counts are finite measurements; the preceding argument
is the all-k bound. No exact formula for total state count is needed.

Ten additional tests cover all 512 subsets of the nine nontautological
clauses on two variables (including the empty clause), 64 seeded random
circuits with both output requirements and three orders, independent
polynomial and truth-table controls, the residual-prefix count, sparse
variable labels, SAT witness checking, invalid inputs, explicit budget
exhaustion, command-line results, and search deeper than 1,000 variables.
The random circuits have 1–5 inputs, 14 gates, repeated wires and fanout.

Counters record interned nodes, expanded states, cofactor node visits and
selected normalization operations. `work_units` **is not a bit-operation
or runtime bound**: sorting, hashing, set unions, label bit lengths and
memory also cost work. The state lower bound already disproves a uniform
polynomial bound for this candidate. Measuring only the final shared DAG
or the successful branch would miss these costs. Budgets are experimental
limits, not strict process memory or CPU limits.

## Run it

The CLI input is a JSON object with `clauses`, and optionally `order` (each
appearing variable exactly once). Signed nonzero integers are literals.

```sh
python3 scripts/solve_shared_dag.py - <<'JSON'
{"clauses": [[1, 2], [-1, 2], [-2, 3]]}
JSON
python3 experiments/shared_dag_sat.py --out-dir reproduced
PYTHONPATH=src python3 -m unittest discover -s tests -p test_shared_dag_sat.py
python3 scripts/reproduce.py --out-dir reproduced --check
```

CLI exit codes are SAT=10, UNSAT=20 and UNKNOWN=0, with the result and
counters in JSON. Defaults cap expanded states at 100,000, interned
nonconstant nodes at 200,000 and work units at 5,000,000. The Python API
accepts `None` for an uncapped resource; disabling caps does not make the
method polynomial or remove finite hardware limits.

## Decision for the complete-proof objective

The specific assertion that sharing plus these local rewrites bounds all
searches polynomially is rejected. Keep the solver and the family as a
regression test, rather than spend another cycle enlarging the same fixed
order benchmark. The selector-first control supplies a successful repair
on this family, not a new proof candidate.

A replacement claiming P=NP still needs a **uniform all-input bound on
total computation**, including the discovery of useful variables or
equivalences. Treating semantic equivalence of arbitrary residual circuits
as a free operation would already supply general circuit UNSAT testing
(compare a circuit with zero), which is the missing problem. The current
work supplies neither that operation nor an argument excluding all other
algorithms. The complete-proof goal remains unmet.
