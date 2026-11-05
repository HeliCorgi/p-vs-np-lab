# Finite audit of the common-annihilator simulation

The [mathematical criterion](affine_dag_annihilator.md) and its
[expander application](expander_separated_space.md) are paper arguments.
This note specifies exactly which components have executable or formal
checks. None of the finite checks proves an asymptotic lower bound by itself.

## 1. Source DAGs and ordinary-PC traces

[`src/pnp_lab/affine_dag_pc.py`](../src/pnp_lab/affine_dag_pc.py) accepts a
finite `semantic-affine-dag-v1` certificate. Its initial nodes must equal
the cited proper raw CNF clauses. Every inference has one or two earlier
parents, which may be reused, and the last node must be the actual empty
clause. The checker evaluates the original affine clauses over the complete
small Boolean cube and verifies each semantic implication. It does not
trust a claimed rank or an algebraic encoding when checking soundness.

Separately, Gaussian elimination finds a basis of the equations defining a
clause's falsity flat. Their product supplies an ordinary polynomial
indicator. An inconsistent falsity system is handled as a tautology with
indicator zero, not as a rank-zero nonempty flat.

Given a rank threshold and a supplied polynomial `mask`, the converter
checks that the mask vanishes on every discarded high-rank flat. It then
implements the weighted replay from the paper proof. Its final polynomial
is the mask. **This is a derived consequence, not necessarily the constant
one or a refutation.** The lower-bound proof needs the separate assertion
that a nonzero mask lies in a space separated from all such consequences.

Every correction is generated from explicit Boolean axioms. For a repeated
monomial, the converter telescopes one repeated power at a time, using
$x_i^2+x_i$ multiplied by the remaining monomial. It first checks that the
squarefree remainder is zero, and then supplies the ordinary derivation of
the unreduced polynomial. Repeated variables remain in all proof lines.

The completed proof is replayed by the earlier independent ordinary-PC
checker in [`parity_pc.py`](../src/pnp_lab/parity_pc.py), with an **empty
assumption context** and the claimed bound $\deg(f)+3R$. Input, Boolean,
addition and single-variable multiplication steps are the only nonzero
rules. No high-rank clause is inserted as a new polynomial axiom.

The finite auditor has explicit caps: 4,096 Boolean assignments, one
million charged semantic literal visits, two million pairs in an individual
sparse product, mask degree 64, and the existing PC trace caps of 200,000
nodes and two million monomial occurrences. These are implementation
limits, not restrictions in the mathematical theorem. Exhaustion is an
error/failed audit, not a proof of nonexistence. There is no claim of a
polynomial-time general certificate-conversion algorithm or proof discovery.

## 2. What the deterministic report checks

[`results/affine_dag_pc.json`](../results/affine_dag_pc.json) records:

- Two masked conversions of an explicit source DAG containing both forms
  of high-parent inference, ordinary low-parent inference, semantic
  weakening, a tautology, and reused earlier nodes. One mask is a genuine
  parity of two coordinates; the other has ordinary degree two and an
  unreduced square. Each final trace is independently replayed.
- Explicit degree-preserving Boolean-ideal proofs for all 27 repeated
  monomials through degree four in three variables, using the basis
  $m+\operatorname{ml}(m)$. These span the entire kernel of Boolean
  evaluation in that finite polynomial space: its dimension is $35-8=27$.
- Every one of the 52 affine flats of the three-dimensional binary cube,
  including the empty flat. Indicators are compared with direct evaluation;
  a consistent rank-$r$ system has exactly $2^{3-r}$ points.

The source fixtures are tiny easy UNSAT formulas. Their purpose is to
check a proof transformation, not to instantiate the asymptotically hard
expanding family or to measure its minimum proof size. The tests also
reject a mask not vanishing on a discarded flat, an unsound inference,
a changed raw input, a future parent, malformed affine forms, and cap
exhaustion. A no-high-line control derives the constant one.

## 3. Exact support counting and parameter arithmetic

[`results/expander_separation.json`](../results/expander_separation.json)
enumerates all 192 variable subsets in three six-variable controls:
disjoint triples, a linear three-clause cycle, and a four-clause Pasch
configuration with empty boundary. Every clause subset in the specified
support range is examined. Testing only connected clause subsets gives the
same answer as testing every clause subset. Bernoulli probabilities and
the Harris product comparison use exact rational arithmetic.

The cycle has a useful failure control: $T=\{2,4,6\}$ contains none of the
individual clause supports, but is the boundary of all three clauses.
Checking only raw-clause containment would incorrectly call its pooled
support empty. The Pasch configuration fails the required expansion and
has no empty-support monomials under this support cutoff. It is not used
as a hard-family witness.

The report also checks the degree, rank, tail, and dimension-ratio budgets
using exact rational arithmetic at three large formal values of $n$.
No graph with those sizes is built, and no explicit finite existence
threshold is asserted. The asymptotic existence proof remains in the
mathematical note.

[`pc_subspace_audit.md`](pc_subspace_audit.md) supplies a separate complete
PC-space checker. On the first two support controls it verifies joint
separation of the proposed monomial spans, not merely nonmembership of
each generator. Its PHP control shows why the static Macaulay span cannot
replace the dynamic PC consequence space.

## 4. Lean boundary

[`Formal/AffineDAGAnnihilator.lean`](../Formal/AffineDAGAnnihilator.lean)
adds six explicitly audited theorems. The recursive squarefree F2
representation has a unique zero polynomial when it vanishes on every
Boolean word. Three pointwise Boolean identities check the retained-parent
and discarded-parent cases. The remaining theorems evaluate the zero
representation and verify the numerical rank/degree reserve.

These are kernel-checked components. This file does not formalize ordinary
multivariate PC, the rank-nullity criterion, the Mikša–Nordström reduction,
the probabilistic existence argument, or the complete exponential DAG
lower bound. The repository's full theorem dependency audit and finite
reproduction are separate checks, and their successful completion must
not be described as a full Lean proof of the new asymptotic theorem.

## 5. Clarifications found by a fresh adversarial review

A further reviewer, given the two mathematical notes without the authors'
discussion, identified two compatibility justifications that needed to be
written explicitly. Both were repaired in the separated-space note:

- The cited normal-form lemma is worded for a variable absent from a term.
  The added argument treats an already occurring variable using support
  containment and reduction modulo one common ideal. This is needed when
  an ordinary PC step is multilinearized.
- Extending the graph operator to unused ambient variables need not assume
  its idempotence. The added coefficientwise proof shows directly that
  multiplication preserves its kernel, which is the actual invariant.

The common-annihilator note also explicitly declares the trivially
available zero line, resolving the degree-zero convention in the
Boolean-zero lemma. These were mathematical interface checks; the successful
finite tests did not by themselves supply the missing explanations.
