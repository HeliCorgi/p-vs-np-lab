# Finite replay of ordinary-PC parity discharge and weighted tree gluing

The [mathematical bridge](parity_pc_bridge.md) converts a parity-query tree
with ordinary $\mathbb F_2$ polynomial-calculus (PC) refutations at its leaves
to an unconditional PC refutation. If leaf $\lambda$ has degree at most
$d_\lambda\ge2$, its weighted consequence is

\[
                2^{D_{\rm PC}(F)}\le\sum_\lambda2^{d_\lambda}.
\]

This audit checks the algebraic conversion using explicit finite traces.
It does not estimate the minimum PC degree from these traces. In particular,
the balanced full-cube examples below have a much simpler direct proof:
adding all their raw clause polynomials gives one at degree equal to the
clause width. The larger degrees recorded below measure this specific
conversion's overhead.

## 1. The implementation checks ordinary polynomials

[parity_pc.py](../src/pnp_lab/parity_pc.py) is deliberately separate from the
earlier Boolean-quotient PC engine. A monomial is a sorted tuple of original
variable IDs **with repetitions retained**. Thus `(1,1,2)` means
$x_1^2x_2$ and has ordinary degree three. The operations are:

| Operation | Meaning |
|---|---|
| `input` | The ordinary product of the false-literal factors of a cited original clause |
| `boolean` | The explicit polynomial $x_v^2+x_v$ |
| `assumption` | An affine equation from the caller-supplied path context |
| `add` | Sum of two earlier polynomials over $\mathbb F_2$ |
| `multiply` | Product of one earlier polynomial by one original variable |
| `zero` | The zero polynomial, a legal zero linear combination |

There is no reduction by $x_v^2=x_v$. The independent replayer expands
raw axioms by counting formal factor choices, counts coefficients modulo
two, and checks every resulting polynomial's actual degree. A certificate's
declared degree must equal the maximum in its trace. The checker receives
all permitted affine assumptions separately; an unstated path equation
cannot be introduced through certificate metadata. Root verification uses
an empty context and requires the final formal polynomial to be one.

The builder and replayer use separate expansion routines. Both retain
literal multiplicities and sparse numeric variable IDs. Their Python
implementations are not formally verified.

## 2. Discharge and composition are actual arithmetic traces

`discharge_parity_pc` consumes a checked proof of one from a context
$\Gamma$ and one additional affine axiom $a=0$. It transforms each line
$p$ to $(1+a)p$. Multiplication by the affine factor is expanded into
individual variable multiplications and additions. The deleted axiom's
image is derived from explicit Boolean axioms using

\[
             a(1+a)=a+a^2=\sum_{v\in\operatorname{supp}(a)}(x_v+x_v^2).
\]

The affine constant cancels in this identity, including when $a$ has
constant term one. The returned root is $1+a$, generally not a refutation
by itself. Every use of the selected axiom has been removed; remaining
ancestor assumptions retain their exact original meanings.

`glue_parity_pc` checks both children under the same ancestor context and
the two opposite answers to a query. It discharges the child with smaller
certified rank, copies that resulting derivation into the common context,
and substitutes its final polynomial for the other child's query axiom.
The entire resulting trace is checked again. For ranks $u,v\ge2$, the
reported parent rank is $u+1$ when they agree and $\max(u,v)$ otherwise.
Ranks must bound the actual ordinary degree of the supplied child proofs.
The final trace's soundness does not rely on the rank claim.

`parity_tree_to_pc` supplies one concrete source of leaf proofs: an already
checked [raw-clause parity tree](parity_query_audit.md). Gaussian row
combinations derive each falsifying literal value. If $f_i$ are the false-
literal factors of the cited clause, the converter explicitly derives

\[
            1+\prod_i f_i
               =\sum_i(f_i+1)\prod_{j<i}f_j
\]

from those path equations, and adds the raw clause axiom. Inconsistent
paths instead derive one by Gaussian row addition. It then performs the
rank-guided composition bottom-up. `glue_parity_pc` itself also accepts
arbitrary independently checked conditional PC traces, not just these
raw-clause leaf proofs.

## 3. Results of the deterministic audit

The [experiment](../experiments/parity_pc.py) reproduces these exact values:

| Source tree | Leaves | Actual leaf degrees | Weighted leaf mass | Root rank | Actual ordinary root-proof degree | Arithmetic nodes |
|---|---:|---|---:|---:|---:|---:|
| Balanced complete parity blocks, two variables | 4 | Four leaves of degree 2 | 16 | 4 | 4 | 45 |
| Balanced complete parity blocks, three variables | 8 | Eight leaves of degree 3 | 64 | 6 | 6 | 160 |
| Three-variable decision-list comb | 4 | 1, 2, 3, 3 | 24 | 4 | 4 | 35 |

The weight of a leaf of actual degree $t$ is $2^{\max(2,t)}$.
For the comb, the exact rank four is smaller than the uniform estimate
$3+\lfloor\log_2 4\rfloor=5$. At each of its two upper nodes, the low-rank
child is discharged first. The three-variable balanced tree includes a
query of all three variables, and both answers include affine equations
with and without a constant term.

All three unconditional traces replay successfully. There are 13 branch
compositions and 181 intermediate lines containing genuinely repeated
variable powers. Reducing those powers for comparison would conceal part
of the degree cost. Replacing the declared degree by that hypothetical
reduced degree is rejected in all three cases. The actual exported root
proofs contain **no** `assumption` nodes.

The report stores every source formula and parity tree, exact profile and
hash of each regenerated PC trace, and the full first trace as a small
inspectable example. The tests additionally check discharge of either
constant offset, retention/rebinding of an ancestor assumption, forced
selection of the lower-rank right child, incorrect degree claims, malformed
operations, raw-input rebinding, and resource exhaustion.

## 4. Evidence boundary

The polynomial identities and weighted theorem are proved in the linked
mathematical note; these finite traces check their implementation on the
specified controls. Neither the traces nor a successful small audit
formalize the entire general theorem. The Lean rank lemma mentioned in
that note covers the abstract counting step, not this Python code or the
ordinary-PC deduction transformation.

Only a **degree** bound is claimed for repeated discharge. Multiplying by
wide affine forms can enlarge sparse polynomials repeatedly. The converter
has explicit node and monomial caps and returns `UNKNOWN` if they are
exhausted. That output says nothing about satisfiability, optimal proof
degree, or nonexistence of a shorter proof. No polynomial bound on the
fully expanded conversion or general SAT algorithm follows.

```bash
PYTHONPATH=src python -m unittest discover -s tests -p 'test_parity_pc.py' -v
PYTHONPATH=src python experiments/parity_pc.py --out-dir reproduced/parity-pc
```
