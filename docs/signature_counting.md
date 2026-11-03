# Exact counting with group-local CNF and XOR signatures

The [implementation](../src/pnp_lab/signatures.py) counts assignments by
enumerating small variable groups, combining assignments that have the same
effect on the XOR equations, and joining the resulting multiplicities.
All non-tautological CNF clauses must stay within their assigned group; XOR
equations can couple every group. A single group containing the whole scope
accepts arbitrary CNF, but then construction enumerates all `2^n` assignments.

This is concrete reuse of the finite measurement/fiber sum-product identity
in `openai/math` family 378. The pinned
[upstream excerpt](../third_party/openai_math/paper/measurement-separation-excerpt.tex),
[source manifest](../third_party/openai_math/manifest.json), and
[reuse audit](openai_math_reuse.md) record its origin and scope. Our code is
an independently written specialization over `GF(2)`, with local Boolean
constraints and integer multiplicities. It does **not** implement the
upstream subexponential algorithm, its rational polynomial replacements,
or its interpolation construction. The [prior-work note](prior_work.md)
separates those external claims and their formalization status.

The useful result is exact counting with costs governed by local assignment
enumeration and signature support sizes. Those sizes can be exponential.
The counterexample in Section 6 proves this for every group width, even when
the original XOR system is immediately solvable by linear algebra.

## 1. Input contract and Python API

```python
from pnp_lab.affine import AffineRelation
from pnp_lab.signatures import count_by_signatures

affine = AffineRelation.from_named(
    ("a", "b", "c", "d"),
    [(("a", "b", "c", "d"), 0)],
)
cnf = ((1, 2), (-1, -2), (3, 4), (-3, -4))
result = count_by_signatures(
    affine,
    cnf,
    groups=(("a", "b"), ("c", "d")),
    max_group_assignments=8,
    max_join_products=2,
)
assert result["status"] == "SAT"
assert result["model_count"] == 4
```

DIMACS literals refer to positions in `affine.variables`; group entries are
variable **names** from that same explicit scope. Groups must be disjoint
and cover every scoped variable, including unconstrained variables. Their
order and the order of names inside a group can change the representative
witness and intermediate supports, but not the final count. Empty groups
are permitted: they have one empty assignment and zero XOR contribution.

The routine validates all literal types and ranges before normalization.
It removes duplicate literals, duplicate clauses, and tautological clauses.
It then checks that every remaining nonempty clause belongs to one group.
A cross-group clause raises `ValueError` with an explicit unsupported-input
message. This restriction is checked even if another clause or the XOR
system already supplies a contradiction. It prevents an unsupported
constraint from being silently ignored. A tautology can span groups and is
removed only after all its literals have been validated.

After those checks, an empty CNF clause or inconsistent input XOR system
returns exact count zero without table enumeration. With no variables,
no constraints, and no groups, the unique empty assignment has count one;
both budgets can be zero in this case.

The XOR rows used by this API are `affine.equations`, which `AffineRelation`
has already normalized. Thus `signature_bits` and
`input_affine_row_count` count those normalized rows, not the raw rows passed
to an earlier constructor. The constructor's normalization is an existing
trust boundary and incurs its own polynomial work.

## 2. Exact counting identity

Write the normalized XOR system as

\[
 Mx=b \quad\text{over }\mathbb F_2,
\]

with `m` rows and `n` variables. Let `S_1,...,S_r` be the disjoint variable
groups. Let `F_g` contain the CNF clauses supported entirely in `S_g`, and
define

\[
 A_g=\{u\in\{0,1\}^{S_g}:F_g(u)\},\qquad
 \sigma_g(u)=M|_{S_g}u\in\mathbb F_2^m.
\]

Signature bit `j` records the contribution of this group to XOR row `j`.
It does not test that row's right-hand side separately. A cross-group
equation is satisfied only after the contributions have been combined.

The table stores exact multiplicities

\[
 T_g(s)=|\{u\in A_g:\sigma_g(u)=s\}|.
\]

The full number of satisfying assignments is

\[
 \#(Mx=b\land F)=
 \sum_{s_1\oplus\cdots\oplus s_r=b}\prod_{g=1}^r T_g(s_g).
 \tag{1}
\]

**Proof.** Every full assignment restricts to one assignment in each group,
and every tuple of local assignments combines into exactly one full
assignment. It satisfies the CNF precisely when each restriction belongs
to `A_g`, because every clause is local. Linearity gives
`Mx = sigma_1(x_1) XOR ... XOR sigma_r(x_r)`. Conditioning on those
signatures partitions the assignments into disjoint fibers. Each fiber has
the product of its local multiplicities, proving (1).

The algorithm evaluates (1) by successive XOR convolution. Initially
`C_0(0)=1`, with all other values zero. For each next group,

\[
 C_i(t)=\sum_s C_{i-1}(t\oplus s)T_i(s).
\]

Inductively, `C_i(t)` counts exactly the assignments to the first `i`
groups that satisfy their local CNF and have accumulated XOR signature `t`.
The answer is `C_r(b)`. Counts are integers, so assignments sharing a
signature are added, not merged into one model. With `m=0`, the only
signature is the empty vector, and the routine multiplies the local model
counts.

### Original-variable witnesses

Each nonzero local table entry keeps one satisfying local assignment with
that signature. Each nonzero convolution entry keeps one compatible pair
of representatives. Because the groups are disjoint, their bitwise union
is a valid assignment to the processed variables; it needs no extra
consistency test on shared variables. At the target signature it satisfies
the entire normalized XOR system and original CNF.

Before returning SAT, the implementation also calls the independent direct
`check_sat_witness` evaluator on the original supplied affine relation and
raw CNF. This checks the witness, not the exact model count. The API does
not emit a separately checkable count or UNSAT proof object. The counting
identity above is a mathematical correctness argument; the tests validate
its implementation on finite cases.

## 3. Costs and observable statistics

Let `b_g=|S_g|`, `t_g=|supp(T_g)|`, and
`d_i=|supp(C_i)|`, with `d_0=1`. A completed run with nonempty local tables
tests exactly

\[
 Q=\sum_g2^{b_g}
\]

local assignments and executes exactly

\[
 P=\sum_{i=1}^r d_{i-1}t_i
\]

pairs of table entries in the convolution. These are the two independently
budgeted operations. We always have

\[
 t_g\le\min(2^{b_g},2^m),\qquad d_i\le2^m,
\]

but none of these quantities has a universal polynomial bound.

Each visit checks local CNF and computes an `m`-bit signature. Counts have
at most `n+1` bits and witnesses have at most `n` bits. These bit operations,
input validation, normalization, and dictionary bookkeeping are additional
work. The counters are not unit-cost machine-step or wall-clock bounds.
Python dictionaries also do not provide a worst-case constant-time lookup
theorem; a conservative worst-case accounting can charge a factor linear
in the largest relevant table for a lookup. No exponential lookup table
or local counting oracle is treated as free.

The implementation retains all local tables plus the old and new join
tables. Its storage is polynomial in the input bit length times
`sum(t_g) + max(d_i)`, up to bookkeeping factors. This can be exponential;
the upstream polynomial-space claim does not apply to this implementation.

| Result field | Meaning |
|---|---|
| `signature_bits`, `input_affine_row_count` | Number `m` of normalized XOR rows. |
| `max_block_size`, `group_sizes`, `groups` | The explicit partition used. |
| `group_assignments_tested` | Total local assignments actually tested. |
| `group_assignments_tested_by_group` | Per-group totals; unvisited groups remain zero. |
| `group_valid_assignment_counts` | Assignments passing the local CNF among those tested. |
| `group_signature_counts` | Number of nonzero entries discovered in each local table. |
| `group_tables_complete` | Whether each entire local table has been enumerated. |
| `dp_state_counts` | The initial singleton state followed by sizes of completed joins. |
| `dp_states_peak` | Largest individual join table reached, including a partial join. It is not total simultaneous memory. |
| `join_products`, `join_products_by_group` | Actual multiplied entry pairs, total and per group. |
| `join_groups_completed` | Number of fully completed joins. |
| `join_partial_group_index`, `join_partial_state_count` | Identify an interrupted join and its partial support size. |
| `model_count`, `witness_mask`, `witness` | Exact count after a conclusive run and a complete original-scope witness when positive. |

## 4. Budgets and exactness

`max_group_assignments` and `max_join_products` are separate, global totals,
each either `None` or a nonnegative integer. They are checked before the
next operation. Completing the entire necessary computation with exactly
the allowed number of operations succeeds.

If a table or convolution is interrupted, the result is `UNKNOWN`,
`exhaustive=False`, `model_count=None`, and no witness. Even if a partial
sum already has a positive target entry, this counting API waits for a
complete count. Partial zeros cannot justify UNSAT. A fully enumerated
empty local table does prove count zero, so later groups and all joins can
be skipped. Similarly, the validated immediate contradictions in Section 1
need neither budget.

Here `exhaustive=True` means the count is conclusive by the stated rules.
It does not mean that every global assignment was visited. In a local
contradiction case, some `group_tables_complete` flags can still be false.

## 5. Useful families and independently checked results

The [experiment](../experiments/signature_counting.py) emits deterministic
JSON with `all_checks_passed`, per-case work counters, and `summary`. Run it
with:

```bash
python experiments/signature_counting.py --out-dir results
```

### Exactly-one triples with one global XOR

Take `B` disjoint triples, require exactly one true variable in each triple
using local CNF, and constrain the XOR of all `3B` variables. Each triple
has three models, all of local signature `1`. Therefore the matching global
parity has exactly `3^B` models; the opposite parity has zero models. Either
case uses `8B` local assignment tests, one signature per group, and `B`
join products.

The measured cases reach **256 triples, 768 variables, and `3^256` models**
with **2,048 local assignment tests and 256 join products**. These are actual
counter values, not a comparison of elapsed solver runtimes.

### Two independent XOR observations

For the same triples, let one row observe the first coordinate of every
triple and a second row observe every second coordinate. A local exactly-one
assignment contributes one of `00`, `01`, `10`, each with multiplicity one.
There are three local signatures, and the accumulated support has four
signatures after two groups. Thus the test is not limited to singleton
tables.

For target bits `(p,q)`, the exact count is

\[
 \frac{3^B+(-1)^p+(-1)^q+(-1)^{p+q+B}}4.
\]

This follows by expanding the four characters of `GF(2)^2`, or by the
four-state convolution recurrence. There are three join products for
`B=1`, and `12B-12` for `B>=2`. The experiment checks all four targets for
several sizes through `B=64`; the peak accumulated support is four.

### Raw semantic oracle and boundary cases

The experiment also compares **144 fixed-seed inputs with at most eight
variables** against **8,176 complete assignments**, evaluated directly on
the raw XOR rows and raw signed CNF. It obtains 110 SAT and 34 UNSAT cases.
The [test module](../tests/test_signatures.py) adds 198 independently
generated cases, group and member-order permutations, multiplicity checks,
unconstrained variables, all target signatures, empty scopes, malformed
inputs, cross-group rejection, and exact versus interrupted budget limits.
The twelve test methods pass. The raw oracles do not reuse Gaussian
normalization, CNF normalization, table construction, or convolution.

## 6. An all-size explicit-table barrier

For any `b>=1`, use one group of `b` variables, no CNF, and the `b` XOR rows

\[
 x_1=0,\ldots,x_b=0.
\]

The normalized measurement matrix is the identity `I_b`. The group
enumerator filters only by local CNF, so it accepts every local assignment.
Its signature is

\[
 \sigma(u)=I_bu=u.
\]

Hence there are **exactly `2^b` distinct local table entries**, each with
multiplicity one. The first join also visits `2^b` products and constructs
`2^b` states, even though the target is zero and the unique final model is
the all-zero assignment. This proves the growth for every `b`; experiments
measure `b=1,...,14`, reaching 16,384 entries.

The proof identifies a limitation of this explicit table algorithm and
its sufficient-signature representation. Gaussian elimination solves the
underlying family directly. Pruning local assignments using XOR targets,
representing a table symbolically, or using a different decomposition can
change the algorithm and its costs. Nothing here excludes those approaches
or proves a lower bound against general SAT algorithms.

For arbitrary inputs, choosing one whole-scope group also shows why the
existence of a valid partition is insufficient: its local enumeration alone
has `2^n` visits. Establishing `P = NP` through a group method would require
a polynomially constructible structure and polynomial total work on every
instance, including cases where the present tables become large.
