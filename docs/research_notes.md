# Research note 001: boundary relations and the cost of eliminating interiors

2026-11-04 JST

## Question and result

The starting question is whether small pieces of a constraint problem can be
summarized by small exact boundary relations, then composed to obtain an
efficient decision method. An output language can become much larger after
existential elimination, even when the original constraints are small and the
resulting relation is easy to evaluate in a different language.

This work supplies elementary proofs, known-result reproductions, and an exact
reference implementation. It supplies no resolution of P versus NP and makes
no novelty claim for the mathematical facts below.

## Claim ledger

| ID | Statement | Evidence | Limitation |
|---|---|---|---|
| F1 | Independent interiors compose by conjunction of their boundary relations | `Formal/BoundaryComposition.lean` | The joint predicate must have the stated factorization; geometry or missing cross-edges are not inferred |
| F2 | The five-color, five-terminal star projects to the existence of an equal terminal pair | `Formal/StarProjection.lean`, finite kernel decision | Exactly the specified finite palette and ordered ports |
| F3 | Every exact auxiliary-free CNF for F2 has a clause containing all ten terminal-pair equalities | Symbolic Lean proof for arbitrary finite CNFs; explicit ten-witness certificate | Color equality/disequality vocabulary; does not lower-bound arbitrary algorithms |
| E1 | For q colors and q star terminals, the minimum required clause width is q(q-1)/2 | General elementary proof in `projection_barrier.md`; semantic checks q=3..6 | The palette grows together with q; not an unbounded-width result at fixed five colors |
| K1 | Even parity on n variables requires 2^(n-1) ordinary auxiliary-free CNF clauses | Known theorem, self-contained proof in `parity_projection.md`, finite verification n=3..12 | CNF representation only; no circuit or time lower bound; not formalized in Lean here |
| E2 | The implemented GF(2) join and projection agree with brute-force semantics on the tested small systems | 120 fixed-seed projection systems and 80 joins, plus edge cases | Tests are not a formal verification of the Python implementation |
| E3 | Seven XOR chains with n=4..256 project to one parity equation | Exact row elimination and coefficient checks | Full boundary tables only at n<=8; full auxiliary enumeration only at small n |
| R1 | The imported HN saved relation has a unique minimum of four additional two-literal clauses over its fixed common pairwise facts | Independent finite recomputation across 855 canonical states | Saved relation is an input; its original SAT leaves and geometry remain trusted |

The Lean workflow builds both modules, then queries the kernel environment for
the main theorems' transitive axiom dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted by the audit. This is an audit
within Lean's normal trust model, not an independently implemented kernel.

## Why the negative and positive controls belong together

The star example prevents generalizing a compact two-literal boundary formula
from one HN interface to arbitrary future projections. For the five-color
example, a width-ten clause is both necessary and sufficient. It remains a
small formula. The example does not establish exponential growth.

Parity supplies the stronger growth example for ordinary Boolean CNF: a linear
chain of local gates can project to exponentially many necessary clauses.
However, its ordered decision diagram has only two states per noninitial
level, and its native XOR equation has n terms. The implementation constructs
both compact alternatives. The CNF expansion cannot be interpreted as evidence
that parity is computationally difficult.

Affine systems provide an exact closure class. Conjunction joins rows of a
linear system. Existential projection first pivots on hidden columns; each
hidden pivot variable can then be solved, while the surviving boundary rows
express precisely the compatibility conditions. Both operations are
polynomial in the explicit matrix size. Integer bit operations still process
rows of finite, potentially growing length.

General SAT is not contained in this affine class. A nonempty affine solution
set has a power-of-two size, whereas the binary OR relation has three points.
Adding affine auxiliaries and projecting preserves affinity, so it cannot
encode that OR relation exactly. A broader class requires a broader operation
or language, together with an analysis of its cost.

## Conditions an algorithmic argument would need

For this strategy, assess at least four different questions:

1. **Coverage.** Which input constraint systems have an exact representation?
2. **Construction.** What resources are required to find that representation?
3. **Composition.** Do conjunction and the required existential projections
   preserve manageable representations, and at what total bit cost?
4. **Decision.** Can the final relation be tested for emptiness at that cost?

Small representations existing in isolation answer none of the last three
questions automatically. Fast operations on a restricted fragment do not
establish coverage of arbitrary SAT. A lower bound for one chosen language
does not lower-bound every possible decision strategy.

For P=NP, one would need a uniform algorithm covering all inputs of an
NP-complete problem and a polynomial bound in encoded input length, including
preprocessing, representation construction, arithmetic, and decision costs.
For P!=NP, one would need a suitable general impossibility argument, not a
failure of this representation or this implementation.

## Next experiment suggested by these results

The next useful extension is a precisely specified mixture of affine and
non-affine constraints, maintaining join-before-project semantics. Record
boundary width, representation size, intermediate density, construction cost,
and exact fallback cost. At small sizes, compare the full projected truth
table with an independent existential oracle. At larger sizes, keep explicit
certificates and state the validation method.

A successful result would identify an explicitly described class with reliable
closure or a narrowly stated obstruction. It would not automatically apply to
all SAT instances. This note does not schedule future work or claim that the
suggested experiment has already run.

## Provenance and reproduction

New deterministic reports are in `results/`; code hashes are recorded in
`results/RUN_SUMMARY.json`. The historical package is preserved byte for byte
under `experiments/baseline/`, including its own results and manifest. Its
README's standalone command is relative to that directory. From the new root:

```bash
python experiments/baseline/run_all.py --out-dir reproduced/baseline
```

The integrated command also runs the baseline and compares its mathematical
results. Only original timestamp, Python environment, and timing fields are
excluded from that comparison. New reports are compared in full.

```bash
python scripts/reproduce.py --out-dir reproduced --check
lake build Formal
python scripts/audit_axioms.py
```

## Primary references

- [Clay Mathematics Institute, P vs NP](https://www.claymath.org/millennium/p-vs-np/): official status; consulted 2026-11-04 JST.
- [Emdin, Kulikov, Mihajlin, Slezkin, *CNF Encodings of Parity*, MFCS 2022](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2022.47): known auxiliary-free parity CNF bound and the distinction when auxiliaries are permitted. We do not reproduce the paper's stronger new tradeoffs.
- [Darwiche and Marquis, *A Knowledge Compilation Map*, 2002](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/jair/pub/volume17/darwiche02a.pdf): representation languages and parity's compact OBDD versus flat CNF.
- [Gwynne and Kullmann, *On SAT representations of XOR constraints*](https://arxiv.org/abs/1309.3060): context for XOR systems and CNF encodings; no propagation-completeness result is claimed here.
- [Pinned HN source manifest](../experiments/baseline/upstream/SOURCE_MANIFEST.json): exact upstream inputs and hashes for R1.
