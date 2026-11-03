# A constant-block bridge from 3SAT to local CNF and global XOR

This note proves an elementary polynomial-time reduction from 3SAT to a
restricted mixed satisfiability problem. For source formulas with no empty
clause, every target CNF clause lies in a supplied group of at most **five
variables**, and every XOR row contains three fresh helpers that occur in no
other XOR row. Satisfiability remains NP-complete under these restrictions.
This is neither a novelty claim nor a resolution of P versus NP.

The construction is implemented in
[`block_bridge.py`](../src/pnp_lab/block_bridge.py), using the existing
[`three_cnf_to_two_cnf_xor`](../src/pnp_lab/reductions.py) gadget. The relevant
counting algorithm and its semantics are described in
[`signature_counting.md`](signature_counting.md).

## 1. Pad, split occurrences, and enforce agreement

Let the source be a CNF formula `F` with `m` nonempty clauses, each of width
at most three, over an explicitly supplied scope of `n` variables. Literals
may repeat, and clauses may be tautologies. Width counts literal occurrences.

**Pad before copying.** Replace a clause `(l_1,...,l_k)` by the triple

\[
 (l_1,\ldots,l_k,\underbrace{l_k,\ldots,l_k}_{3-k}).
\]

This preserves its truth value. Give every occurrence in these padded
triples a distinct variable, retaining the occurrence's sign. Thus there
are exactly `3m` copy variables. In particular, repetitions introduced by
padding receive distinct copies.

For an original variable `x` with copies `z_1,...,z_t`, do nothing if `t=1`.
If `t>=2`, add the directed implication cycle

\[
 (\neg z_i\lor z_{i+1}\lor z_{i+1})
 \qquad(1\le i\le t),\qquad z_{t+1}=z_1.
\]

Each triple is the implication `z_i -> z_{i+1}`. A satisfying cycle has all
copies equal: any true copy forces every successor true, while if none is
true all are false. Conversely, either constant assignment satisfies it.
These are triples of occurrences; three distinct variables are not required.

Let `E` denote the expanded formula and

\[
 c=\sum_{x:t_x\ge2}t_x,\qquad q=m+c.
\]

Then `c<=3m` and `q<=4m`. Each copy occurs once in a replaced source clause.
A copy in a cycle also occurs once negatively in its outgoing implication
and twice positively in its incoming implication. Hence it has **four
occurrences**, while a copy outside all cycles has one.

A source model lifts to a model of `E` by assigning every copy its original
variable's value. A model of `E` projects to a source model by taking the
common copy value for every used original variable. Unused original
variables can be set to false. Therefore

\[
 F\text{ is satisfiable}\iff E\text{ is satisfiable}.
\]

## 2. Apply the binary-CNF/ternary-XOR gadget

For each expanded triple `(a,b,c)`, introduce fresh helpers `u,v,w` and use

\[
 (a\lor u)\land(b\lor v)\land(c\lor w),
 \qquad u\oplus v\oplus w=0.
\]

If all three literals are false, the binary clauses force all three helpers
to one, contradicting even parity. If some literal is true, set its helper
to zero and the other two helpers to one. The binary clauses and even parity
then hold. Thus, for every fixed copy assignment,

\[
 a\lor b\lor c
 \iff \exists u,v,w:\ (a\lor u)\land(b\lor v)\land(c\lor w)
                    \land(u\oplus v\oplus w=0).
\]

Freshness makes these choices independent across expanded clauses.
Composing this equivalence with Section 1 proves the complete reduction.
The [existing gadget note](two_cnf_xor_reduction.md) gives its corresponding
witness and multiplicity analysis.

For each copy `z`, create a group containing `z` and the helper associated
with each occurrence of `z`. Every helper belongs to exactly one such group.
The groups therefore partition the entire target scope. Every binary clause
joins a copy to one of its own helpers, so its group-local CNF is a star.
The XOR equations can connect different groups.

| Quantity | Bound for `m` nonempty source clauses |
|---|---:|
| Copy variables / groups | `3m` |
| Added cycle clauses | `c<=3m` |
| Expanded triples / XOR rows | `q=m+c<=4m` |
| Helpers | `3q<=12m` |
| Total target variables | `3m+3q<=15m` |
| Binary CNF clauses | `3q<=12m` |
| Variables per group | `2` or `5` |
| Complete local assignment visits | at most `32` per group; `96m` total |

All target CNF clauses here have exactly two literals on distinct variables.
Every XOR row has exactly three distinct helpers; the helper triples are
mutually disjoint. Copy variables appear in no XOR equation.

## 3. The local tables have at most five entries

For a five-variable group, write its coordinates as
`(z,s,o,i,j)`: source helper, outgoing helper, and the two incoming helpers.
Its CNF is

\[
 (\pm z\lor s)\land(\neg z\lor o)\land(z\lor i)\land(z\lor j).
\]

The three incident XOR rows are distinct. Omitting zero coordinates, the
local signature is `(s,o,i XOR j)`. Its exact positive multiplicities are:

| Signature | Positive source occurrence | Negative source occurrence |
|---|---:|---:|
| `(0,0,0)` | 0 | 1 |
| `(0,1,0)` | 2 | 1 |
| `(0,1,1)` | 2 | 0 |
| `(1,0,0)` | 1 | 1 |
| `(1,1,0)` | 3 | 3 |
| `(1,1,1)` | 2 | 2 |

All other signatures have multiplicity zero. To derive the table, condition
on `z`. When `z=0`, the incoming helpers are both one; a positive source
also forces `s=1`, while a negative source leaves `s` free. When `z=1`,
`o=1`, the incoming helpers are free, and a negative source forces `s=1`.
For two free incoming helpers, each parity has two assignments. Summing
these two cases gives ten local models for a positive source and eight
for a negative source, with **five signatures** in either case.

A two-variable group has just `(±z OR s)`: signature zero has multiplicity
one and signature one has multiplicity two. Consequently every local table
on this reduction's image has at most five entries. Signatures still have
up to `4m` bits; an assignment visit is a work counter, not a constant-time
bit operation.

## 4. Restricted satisfiability is NP-complete

Consider the language of satisfiable encoded mixed instances with a supplied
partition into groups of size at most five, group-local binary CNF stars,
and homogeneous ternary XOR rows on pairwise disjoint helper triples.
Designated star centers do not participate in XOR rows. The construction
above maps every 3SAT instance with no empty clause to this restricted class
and preserves its SAT answer. Exactly-three-literal source clauses already
suffice for hardness. Inputs containing an empty clause can be rejected
directly; the API instead returns the unsatisfiable shortcut in Section 6.

The transformation has polynomial bit complexity. It scans at most `3m`
padded occurrences, records their original-variable indices, and creates
at most `4m` expanded triples and `15m` target variables. Indexed fresh names
have polynomial total length. Even dense integer bitmasks for the XOR
matrix use only `O(m^2)` bits; indices and copy maps require polynomially
many bits in the original input length. There is no exponential integer
hidden in a unit-cost representation assumption.

The restricted language belongs to NP: the structural conditions can be
checked in polynomial time, and a certificate gives one bit per target
variable. Evaluate every binary clause and XOR row to verify it in
polynomial time. Standard NP-completeness of 3SAT (see Cook’s
[*The P versus NP Problem*](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf))
and the reduction establish NP-completeness of this restricted SAT language.

The substantive distinction is between constructing local tables and
combining them. For local tables `T_g`, the required count is

\[
 \sum_{s_1\oplus\cdots\oplus s_{3m}=0}\prod_g T_g(s_g).
\]

SAT asks only whether this sum is positive; constructing the exact integer
count is an additional output requirement, not a prerequisite for `P=NP`.
Constant group size and constant local support do not give a polynomial
bound on accumulated signature support. A uniform polynomial-time algorithm
that decides this global compatibility problem on every image of the
reduction would imply `P=NP`. An exact polynomial-time counter would also
decide SAT, but this non-parsimonious reduction proves no equivalence between
SAT decision and exact counting. Conversely, NP-completeness alone proves
no superpolynomial lower bound for every algorithm, or even for an
unspecified alternative join representation.

## 5. An all-size example for the current join implementation

Take `m>=1` disjoint positive clauses, each on three distinct variables.
All copies have one occurrence, so every group has size two and table
`T(0)=1, T(1)=2`. There are `7^m` source models. For one clause, a source
assignment with `s` true occurrences has `2^(s-1)` helper extensions, giving

\[
 \sum_{s=1}^3\binom3s2^{s-1}=3+6+4=13.
\]

Hence the target has `13^m` models. This reduction preserves decisions and
witnesses, **not model counts**.

In source-occurrence group order, the current
[`count_by_signatures`](../src/pnp_lab/signatures.py) retains all completed
XOR-row bits until the final target lookup. After `k` complete clauses its
support is all `2^k` signatures on those rows: each independent row can
have either accumulated parity with positive multiplicity. Joining the
three groups of clause `k+1` visits respectively

\[
 2^{k+1},\quad2^{k+2},\quad2^{k+2}
\]

entry pairs. Therefore, for every `m>=1`,

\[
 \texttt{dp\_states\_peak}=2^m,\qquad
 \texttt{join\_products}=10(2^m-1),\qquad
 \texttt{group\_assignments\_tested}=12m.
\]

The [experiment](../experiments/constant_block_bridge.py) checks finite
members of this family; the argument establishes the formulas for all `m`.
This is a limitation of the present implementation on an easy family.
Component decomposition, or checking and discarding a row as soon as no
remaining group touches it, handles these independent clauses efficiently.
It is not a lower bound against those methods or general SAT algorithms.

## 6. API, edge cases, and proof scope

`three_cnf_to_constant_blocks(variables, clauses)` returns the source scope
and CNF, copy variables and their original-variable map, `expanded_cnf`,
the existing gadget result as `bridge`, and `groups`. The groups contain
**variable names**, as required by `count_by_signatures`. The `lift_witness`
and `project_witness` methods compose agreement of copies with the gadget's
witness maps; unused source variables project to false.
`copy_to_original[i]` is the zero-based source column for `copy_variables[i]`.

The entire input is validated before contradiction shortcuts. If a source
clause is empty, the result uses empty-scope affine truth, one empty CNF
clause, no XOR rows, and `groups=()`. It is unsatisfiable. An empty source
formula instead produces empty-scope truth with no CNF clauses and is
satisfiable. Thus “all binary clauses have exactly two literals” applies
to the nonempty-clause construction; “width at most two” also includes the
empty-clause shortcut.

This note is a mathematical proof accompanied by executable witness checks,
[structural tests](../tests/test_block_bridge.py), and experiment oracles.
It does not claim a Lean formalization of this new reduction. The pinned
`openai/math` material is background for the finite conditioning identity in
[`openai_math_reuse.md`](openai_math_reuse.md); it is not an assumption of
this reduction or its complexity proof.
