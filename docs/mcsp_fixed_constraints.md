# A fixed candidate formula with incremental evidence and explicit extraction

Date: 2026-11-11 JST. Status: two of the requested three uniform guarantees
are obtained. Candidate representation and evidence updates have polynomial
bounds. A complete finite extraction algorithm is implemented, with polynomial
working space, but **its general running time is not proved polynomial**.
This is not a complete solution of the user's requested general guarantee.

The [previous representation](mcsp_region_pruning.md) rebuilt sets of sample
signatures after each new counterexample. Here the entire circuit candidate
space is represented once by an immutable constraint formula. Adding a row
changes a preallocated evidence slot and propagates its consequences; it
does not split candidate states or append constraints. This directly removes
representation growth and repeated reconstruction from that part of the
algorithm. Extraction work remains separately visible.

## Universal circuit encoding

Let N=2^n be the explicit truth-table length and let s be the gate budget.
The basis is NOT, AND and OR, with free constants/input wires and unrestricted
fan-out. Gate i can select parents only among its m_i=n+2+i preceding wires.
There are exactly s gate slots. A circuit with fewer gates is padded with
unused NOT(False) gates; its output can still select an earlier wire.

Each slot has three one-hot operator selectors and two one-hot parent
selectors. A separate one-hot group selects the output among m_s=n+2+s
wires. Canonical parent order for AND/OR and a fixed unused second argument
for NOT remove redundant syntax without removing any computed function.

For each of the N input rows, the formula already contains:

- three variables per gate for its selected left value, right value and
  output;
- conditional equalities connecting selected parents to those values;
- the conditional Boolean gate equations;
- one variable O_x for the selected circuit output on that row.

The formula is ordinary CNF, built explicitly in
[mcsp_fixed_constraints.py](../src/pnp_lab/mcsp_fixed_constraints.py).
Exactly-one constraints use an at-least-one clause and pairwise exclusions.
For example, the AND case is encoded by the three usual clauses for
z iff a AND b, each guarded by the operator selector. Multiplexers use two
guarded clauses per possible parent. Constant input values are simplified
when constructing each row. This is a standard bounded synthesis encoding,
not a claim of a new representation technique.

**Exactness.** Any ordinary circuit within the budget has a padded canonical
encoding. Its wire values on every row give a satisfying assignment of the
formula. Conversely, any satisfying assignment selects exactly one operator,
each parent and one output. Parent indices guarantee a DAG. Induction through
the gates forces every evaluation variable to equal the ordinary circuit's
value. Thus adding O_x=t_x expresses exactly consistency with that example.
There are no spurious output values and no assumption that a SAT query is free.

The selector count is

\[
H=3s+2\sum_{i<s}m_i+m_s,
\]

and the total variable count is exactly

\[
V=H+N(3s+1).
\]

Before constant simplification, a clause-count upper bound is

\[
C\le\sum_{i<s}\bigl(7+2m_i(m_i-1)\bigr)
 +1+\binom{m_s}{2}
 +N\left(\sum_{i<s}(4m_i+8)+2m_s\right).
\]

Literal storage has the same polynomial scale. Construction, all row
variables and occurrence lists are charged before any counterexample is
added. The guarantee is polynomial in **N,n,s**. At the project's s=n²
target this is polynomial in N; it is not polynomial in n. Nor is this a
claim of polynomial dependence on log s for an arbitrarily large binary
budget. No reduction from general SAT to polynomial-time extraction has
been supplied.

## Updates do not rebuild or enlarge the formula

The data structure stores N evidence slots, a V-variable root assignment,
a trail with at most V entries, and the immutable formula and occurrence
lists. The active candidate set is

\[
\{w:\exists v\;F_{n,s}(w,v)\ \land\!
        \bigwedge_{x\in E}(O_x=t_x)\}.
\]

Appending a counterexample changes one evidence slot and starts unit
propagation from that output variable. The formula object, variable count,
clause count and literal storage are unchanged. Repeated identical evidence
does nothing beyond the request check; conflicting evidence makes the set
empty. Root assignments contain only logical consequences of the formula
and evidence. Temporary extraction decisions are never retained as facts.

**Total propagation bound.** Root variables are assigned at most once across
the entire monotone sequence of updates. An assignment visits only clauses
containing the newly false literal. For a clause c, at most |c| such visits
can occur, each inspecting at most |c| literals. Consequently, across all
counterexamples together,

\[
\text{root clause visits}\le\sum_c|c|,\qquad
\text{root literal inspections}\le\sum_c|c|^2.
\]

Queue work is O(V), with O(N+V) assignment/request checks for at most N
distinct counterexamples. This is an unconditional polynomial bound for
the update operation, including the propagation actually performed. It does
not assert that unit propagation decides whether the active candidate set
is empty. If it finds a contradiction, emptiness is proved; otherwise the
extractor still has work to do. The runtime asserts both inspection bounds.

Fixed size means fixed formula structure and a fixed polynomial capacity
for assignments, evidence and trails. It does not mean every Python list
already occupies its maximum capacity before the first update.

## Extraction: implemented, with a precise conditional time bound

The extractor searches selector choices and uses the same unit constraints.
It works on a copy of the root assignment and rolls back a bounded trail.
It does not create learned clauses, candidate-state catalogues or an
unbounded proof log. A complete unsuccessful decision tree proves NO.
A work cap yields UNKNOWN, not NO; the root remains reusable afterward.

There is also a constructive saving: only gates reachable from the selected
output are branched on. Once that subcircuit is fixed, every unused slot can
be filled deterministically with NOT(False). This preserves the output and
budget, so unused gate choices need not be enumerated. The complete CNF is
checked before returning a model, and the decoded circuit is separately
verified on the input truth table by the outer loop.

Let G=3s+1 be the number of selector groups, and d_j the number of remaining
choices in each group after root propagation; an already fixed group has
d_j=1. The computable quantity

\[
R=\prod_{j=1}^{G}d_j
\]

bounds all remaining selector combinations. The finite decision tree has
at most O((G+1)R) nodes. Different branches select different values of a
one-hot group, and each path resolves a group at most once. Dynamic traversal
of reachable gates and deterministic padding only omit branches.
Per-node propagation, rollback and bookkeeping take polynomial work in
V and the formula's literal count. Therefore extraction takes at most

\[
O((G+1)R)\,\operatorname{poly}(V,\textstyle\sum_c|c|).
\]

If R is bounded by N^c for a fixed c at every refinement on an input family,
this gives a polynomial extraction guarantee for that family, including all
N+1 calls. This is a usable sufficient
condition, not a proved property of general inputs. The program reports R
and charges its computation; a small formula does not imply small R.

Working memory is polynomial independently of R: one root assignment, one
working assignment, trails of at most V entries, at most G decision frames,
and at most H selector choices across a path. Counters require only logarithmic
space in the total number of tree operations. The outer counterexample loop
has at most N+1 extraction calls. Stored round witnesses and metrics add
polynomial trace space. These space bounds do not make the tree short.

## Finite evidence and disclosed extraction limits

The [experiment](../experiments/mcsp_fixed_constraints.py) first validates
5,223 literal circuit encodings using a separate scalar construction of
their full models. Flipping a row's output value rejects all 20,766 corrupted
models. It then runs the same complete panel of 288 target tables as before.
Every definitive answer is checked against independent semantic enumeration;
every intermediate witness satisfies the retained examples.

The initial extraction limit is 500,000 logical work units per call:

| n,s | Fixed variables / clauses / literal slots | YES | NO | UNKNOWN |
| --- | --- | ---: | ---: | ---: |
| 2,2 | 58 / 270 / 700 | 14 | 2 | 0 |
| 2,4 | 116 / 665 / 1,760 | 14 | 0 | 2 |
| 3,3 | 133 / 850 / 2,209 | 84 | 172 | 0 |

Formula sizes remain unchanged throughout every counterexample sequence.
The UNKNOWN cases are XOR and XNOR at budget four, which are known to be
feasible. Both are retried from scratch with the **same** algorithm at a
5,000,000-unit cap per extraction. They return valid circuits, with total
extraction work of 658,471 and 1,800,435 respectively across their refinement
rounds. Their full follow-up costs, including construction and verification,
are 666,959 and 1,808,923. Both initial failed attempts remain in the results;
the follow-ups are not treated as successes at the original limit.

Primary aggregates, charging construction afresh for every target:

| n,s | Construction | Evidence updates | Extraction | All accounted work |
| --- | ---: | ---: | ---: | ---: |
| 2,2 | 54,544 | 1,360 | 168,238 | 225,430 |
| 2,4 | 131,072 | 1,818 | 1,281,106 | 1,415,590 |
| 3,3 | 2,759,936 | 42,679 | 87,872,094 | 90,727,487 |

The final column also includes input loading and truth-table verification.
The two-input/four-gate total becomes 3,891,472 when both follow-ups are
included. These are logical accounting events, not exact bit operations or
elapsed seconds, and they use a different ledger from the previous methods.
Extraction dominates this implementation's panel; compact representation
and cheap updates have not removed its general search expense.

The [tests](../tests/test_mcsp_fixed_constraints.py) cover every two-input
partial table at budget two, all full two-input targets, fixed shape and
monotone root assignments, timeout recovery, contradictory evidence, invalid
models and skipping unused slots. For three-input AND, raising the budget
from three to six leaves the decision count at 23 because unused slots are
filled without branching. Encoding size and padding work still grow and
are charged.

Full initial runs and follow-ups are stored in
[mcsp_fixed_constraints.json](../results/mcsp_fixed_constraints.json).
The reproduction summary preserves the initial-limit status counts.

```sh
PYTHONPATH=src:. python -m unittest tests.test_mcsp_fixed_constraints -v
PYTHONPATH=src python experiments/mcsp_fixed_constraints.py --out-dir /tmp/mcsp-fixed
python scripts/reproduce.py --out-dir /tmp/pnp-reproduced --check
```

The remaining requested guarantee is general polynomial **time** for exact
emptiness and extraction. The construction proves polynomial representation,
polynomial total evidence propagation and polynomial extraction **space**,
with a conditional time bound and an executable exact search. It does not
prove the remaining time bound, a general MCSP upper bound of N poly(n),
a new circuit lower bound, or either direction of P versus NP. The arguments
in this note are written proofs, not Lean formalizations.
