# One-pass clauses from joint CNF and XOR reasoning

## Result

The new pass uses a native XOR row together with binary CNF clauses to derive
an ordinary clause. It recovers the source clauses hidden by our earlier
3-SAT-to-2-CNF-plus-XOR bridge. The existing exactly-one parity pass can then
refute every odd-cycle member of that bridge family before representative
enumeration. The measured cases include 707 target variables, with a composed
UNSAT certificate checked against the original mixed input.

This closes the specific representation failure in
[the previous parity-cut experiment](parity_cuts.md). It does not make the
solver polynomial on general inputs. Both an exactly-two family and a
connected, arity-three parity family still force its full exponential residual
search. The former is unaffected by the width cap; the latter shows a missing
parity-recovery capability even when every input constraint has arity three.

Implementation: [`joint.py`](../src/pnp_lab/joint.py).
Semantic Lean proof: [`JointXorClause.lean`](../Formal/JointXorClause.lean).
Reproduction: [`joint_reasoning.py`](../experiments/joint_reasoning.py).
Machine-readable results: [`joint_reasoning.json`](../results/joint_reasoning.json).
The actual Lean build and axiom-audit outcome is reported by the repository's
validation workflow; the existence of a source file alone is not that check.

## 1. The rule and its proof

Suppose an input row has support \(H\) and right-hand side \(b\):

\[
\bigoplus_{v\in H}x_v=b.
\]

For every \(v\in H\), choose an actual binary CNF clause
\(g_v\lor p_v\). Here \(g_v\) is a signed literal on \(x_v\), and \(p_v\)
is its partner literal. Write \(\epsilon_v=0\) for a positive pivot and
\(\epsilon_v=1\) for a negative pivot. If

\[
\bigoplus_{v\in H}(1\oplus\epsilon_v)\ne b,
\]

then the mixed input entails the clause

\[
\bigvee_{v\in H}p_v.
\]

**Proof.** Assume all partner literals are false. Every cited binary clause
then forces its pivot literal true, so \(x_v=1\oplus\epsilon_v\) at every
row coordinate. Their XOR disagrees with the required right-hand side, a
contradiction. Therefore at least one partner is true.

For example, an even row on three helpers and three binary clauses gives

\[
u\oplus v\oplus w=0,\qquad
(u\lor a)\land(v\lor b)\land(w\lor c)
\quad\Longrightarrow\quad a\lor b\lor c.
\]

A signed example uses \(x\oplus y=0\), \(x\lor a\), and
\(\neg y\lor b\): false partners would force \((x,y)=(1,0)\), so the
derived clause is \(a\lor b\).

No independence assumption is present. Partners can repeat, have either
sign, or mention other pivot variables. The same binary clause may serve
different row coordinates. Repeated identical partners collapse to one
literal; a conclusion containing both signs of a variable is a tautology and
is omitted. A contradictory empty row can justify the empty clause. A
width-one row can justify a unit clause.

### Why all original models and counts are preserved

Let \(F\) be the original mixed formula and \(D\) the conjunction of all
checked derived clauses. Each rule instance proves \(F\Rightarrow D_i\), so

\[
F(a)\quad\Longleftrightarrow\quad F(a)\land D(a)
\]

for every assignment \(a\) to the **original target variables**. All original
constraints remain. Adding these consequences preserves the complete model
set, hence its cardinality. Applying the existing sound parity cuts afterward
preserves that same set.

This does not make the earlier bridge parsimonious. For one source clause
\(a\lor b\lor c\), the source has seven models while the six-variable mixed
target has thirteen. The experiment explicitly checks that the joint solver
returns thirteen target models. It does not mistake source-model counts for
target-model counts.

The Lean module proves the signed implication for arbitrary finite lists, and
then proves pointwise model preservation and satisfiability preservation when
justified clauses are added. It does not formalize the Python search,
normalization, JSON checking, Gaussian elimination, or its runtime.

## 2. Discovery has a fixed polynomial budget

`MAX_JOINT_ROW_WIDTH = 3` is a constant in the implementation. The pass examines
only the normalized **input XOR rows** and binary clauses from the **original
raw CNF**. It does not enumerate the XOR row space, iterate to a fixed point,
or use newly derived clauses as premises during this pass.

Let \(r\) be the number of input rows and \(m\) the number of raw CNF
clauses. For one row coordinate there are at most \(m\) binary choices, since
a non-tautological binary clause can supply at most one signed pivot on that
variable. Therefore a row of width at most three has at most
\(\max(1,m)^3\) candidate premise selections. The whole pass examines at
most

\[
r\max(1,m)^3
\]

candidates, with polynomial work on the explicit input per candidate.
Duplicate binary clauses are deduplicated before this search. New clauses
are also deduplicated and are omitted when already present in normalized
input CNF. There are only
\(\sum_{j=0}^{\min(n,3)}2^j\binom nj=O(n^3)\) distinct non-tautological
conclusions of width at most three, including the empty clause.

The fixed cap matters. If a row width \(w\) were an unrestricted input
parameter, the same discovery procedure would allow \(m^w\) choices. A
semantic theorem for arbitrary width does not make that search polynomial.

`max_cells` limits the subsequent representative search. It does not charge
these polynomial preprocessing passes. A zero-cell budget can therefore
produce a checked UNSAT proof, or `UNKNOWN` when preprocessing does not settle
the input. Invalid Boolean flags and invalid budgets are rejected before
preprocessing shortcuts, including on already contradictory input.

## 3. Certificate format and independent checking

`derive_joint_clauses(affine, cnf)` returns a
`joint-xor-binary-clauses-v1` object. Each step contains:

| Field | Meaning |
|---|---|
| `xor_row` | Index into the normalized input `AffineRelation.equations` |
| `premises` | One entry for each row-support coordinate, in increasing variable order |
| `pivot_literal` | Signed pivot literal in the cited binary clause |
| `clause` inside a premise | Index of that premise in the original raw CNF |
| `clause` at the step level | Normalized disjunction of partner literals |

`check_joint_clause_certificate` reconstructs the cited binary clauses with a
separate normalization routine, checks the row support and forced parity,
and checks the exact partner disjunction. It accepts only sound strengthening
steps; it does not claim that every possible consequence was discovered.
The reported candidate counter is range-checked, not independently recomputed
as an exhaustive search certificate.

The proof checker does not call the joint finder, the parity finder, a SAT
solver, or Gaussian elimination for this implication check. The tests replace
those helpers with functions that raise, then check a short composed UNSAT
proof successfully. This tests implementation separation; it does not make
Python or input normalization formally verified.

`solve_with_joint_reasoning` augments the original CNF with the checked
conclusions and calls `solve_with_parity_cuts`. Its final UNSAT wrapper has
kind `joint-xor-cnf-unsat-v1` and contains `joint_derivation` plus `residual`.
`check_joint_unsat_certificate` starts from the original mixed input,
reconstructs the augmentation, and checks the residual parity-cut proof on
that augmented formula. An original-input SAT witness is checked directly.

The normalization of `AffineRelation` and the Python runtime remain trusted.
A residual enumeration certificate inherits the earlier checker's documented
trust scope and may be exponentially long. SHA-256 digests in the report
identify exact certificate data; they do not replace proof checking.

## 4. The bridge odd-cycle obstruction is removed

For odd \(k\geq3\), start from a cycle with the two clauses
\((x_i\lor x_{i+1})\) and \((\neg x_i\lor\neg x_{i+1})\) on each edge.
They require alternating bits around an odd cycle, which is impossible.

The bridge introduces three fresh helpers per source clause, an even XOR row
on each helper triple, and one binary clause per helper. Thus it has
\(7k\) target variables, \(6k\) binary clauses, and \(2k\) independent
native XOR rows. Every target variable is observed in the CNF, so the previous
quotient algorithm has dimension and observed rank \(5k\). The CNF-only
exactly-one pass found no usable cuts in that representation. Its full search
has \(2^{5k}\) cells, as established in the earlier experiment.

The new joint rule has exactly one binary premise choice at each helper.
It reconstructs each padded source clause, with repeated partners removed.
There are \(2k\) candidate selections and \(2k\) new source clauses. The
existing parity pass can now derive the edge equations
\(x_i\oplus x_{i+1}=1\). XORing all \(k\) edges cancels every variable and
leaves \(0=1\). This argument works for every odd \(k\), with polynomial
discovery and a polynomial-size certificate in the explicit input encoding.

| Cycle \(k\) | Target variables | Old full search | New measured cells | Original-input certificate |
|---:|---:|---:|---:|---|
| 3 | 21 | 32,768, measured previously | 0 | Accepted |
| 5 | 35 | \(2^{25}\), predicted | 0 | Accepted |
| 11 | 77 | \(2^{55}\), predicted | 0 | Accepted |
| 33 | 231 | \(2^{165}\), predicted | 0 | Accepted |
| 101 | 707 | \(2^{505}\), predicted | 0 | Accepted |

The experiment reads the earlier 32,768-cell measurement from
[`results/parity_cuts.json`](../results/parity_cuts.json), checks its status,
and records its file and case digests. It does not repeat the old search.
The larger old counts are mathematical predictions, not timed or enumerated
runs. Zero cells means that preprocessing proved UNSAT, not that computation
was free.

Recovering the source clauses is useful for every bridge instance, but then
solving arbitrary recovered 3-SAT remains the original difficult task.
The odd-cycle family has a short additional parity argument; general 3-SAT
does not acquire one merely because its clauses have been recovered.

## 5. Two explicit infinite families still evade these passes

### Exactly two true variables against odd parity

For \(n\geq4\), use the CNF consisting of

\[
\bigwedge_{i=1}^n\left(\bigvee_{j\ne i}x_j\right)
\quad\land\quad
\bigwedge_{\{i,j,k\}\subseteq[n]}(\neg x_i\lor\neg x_j\lor\neg x_k).
\]

The first part requires at least two true variables; the second permits at
most two. Add the native row \(\bigoplus_{i=1}^n x_i=1\). The CNF has exactly
\(\binom n2\) models, all with even parity, while the row has
\(2^{n-1}\) models. Their conjunction is UNSAT.

Every CNF clause has width at least three. Thus there is no binary premise
for joint inference and no binary exclusion for the exactly-one parity
recognizer. The native row also has width greater than three. Neither pass
adds anything. All variables are observed, so the fallback still checks
exactly \(2^{n-1}\) cells. The formula is connected through the native row;
this is not disconnected padding or an explicit false singleton clause.

Its ordinary literal encoding has length \(\Theta(n^3\log n)\), so this
search is superpolynomial in input length. Measured \(n=4,6,8,10,12,14,16\)
cases agree with the formula, ending at 32,768 cells. Every corresponding
zero-cell run returns `UNKNOWN`. A cardinality-aware algorithm can refute
this family easily; the statement concerns this implemented algorithm.

### A connected cubic prism with hidden parity equations

For each \(k\geq3\), take two length-\(k\) cycles joined by \(k\) matching
rungs. This connected cubic prism graph has \(2k\) vertices and \(3k\)
edges. Assign one Boolean variable to each edge.

Choose one vertex with charge one and express its three-edge parity as a
native XOR. Give all other vertices charge zero and encode each even parity
as the four width-three CNF clauses excluding its odd assignments. The
result has \(3k\) variables, one native width-three row, and \(8k-4\)
width-three clauses. There are no binary clauses.

The mixed input is UNSAT for every \(k\): XORing all vertex parity equations
counts every edge twice, giving zero on the left and the single odd charge
one on the right. Each component alone is satisfiable. The CNF accepts the
all-zero assignment; the native row accepts an assignment with one incident
edge true. The construction is connected and all constraints have arity
three.

The joint pass has no binary premises. The exactly-one recognizer has no
binary exclusions. Every edge is observed by the CNF at its other endpoint,
so the one independent native row leaves dimension and observed rank
\(3k-1\). The implemented fallback therefore visits all \(2^{3k-1}\)
cells. Its ordinary literal input length is \(\Theta(k\log k)\).

| Prism cycle \(k\) | Variables | Width-three clauses | Measured cells |
|---:|---:|---:|---:|
| 3 | 9 | 20 | 256 |
| 4 | 12 | 28 | 2,048 |
| 5 | 15 | 36 | 16,384 |

This is a Tseitin-style parity contradiction. Ordinary CNF parity-pattern
recovery would recognize the four-clause vertex blocks, reconstruct their
XORs, and let Gaussian elimination refute the whole instance. The present
implementation lacks that recovery step. The family documents that missing
capability and the exact current search cost; it is not a lower bound against
modern CNF-XOR solvers or arbitrary SAT algorithms.

## 6. Evidence and relation to prior work

The experiment uses seed `2026110404` for 160 raw-input oracle cases with one
to seven variables. It checks all 5,714 original assignments across those
cases, directly evaluating the input rows and signed clauses before solver
normalization. It compares the exact original and strengthened model sets,
both solvers' model counts, SAT witnesses, and every UNSAT certificate.
There are 63 SAT and 97 UNSAT cases. Each case has an input digest and compact
outcome data in the report. One small complete composed proof is included.

[`tests/test_joint.py`](../tests/test_joint.py) additionally checks all 168
signed forcing patterns through width three, repeated and overlapping
partners, tautological conclusions, reused binary premises, corrupted proofs,
empty rows and clauses, JSON round trips, and invalid budgets or flags.
These finite tests support the implementation; the all-size family arguments
above are mathematical proofs about its specified passes and fallback.

The inference follows established explanation-based CNF-XOR reasoning.
[Laitinen, Junttila, and Niemelä's DPLL(XOR) work](https://arxiv.org/pdf/1407.6571)
uses an XOR module to explain implications and conflicts to a clausal search.
[Soos, Gocht, and Meel](https://pmc.ncbi.nlm.nih.gov/articles/PMC7363182/)
integrate Gauss–Jordan reasoning with CNF search and explanation generation.
Our pass is a deliberately restricted, proof-producing instance of that
principle. It is not a novelty claim for mixed reasoning, a general CDCL(XOR)
implementation, or a polynomial-time proof-search theorem. See
[the prior-work review](prior_work.md) for the relevant proof-system and
certification context.

Reproduce this phase with:

```bash
python experiments/joint_reasoning.py --out-dir reproduced
PYTHONPATH=src python -m unittest discover -s tests -p test_joint.py -v
```

The report sets `all_checks_passed` only after the asserted conditions succeed.
Its `algorithm_general_polynomial_time` field remains `false`.
