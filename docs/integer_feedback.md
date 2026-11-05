# Feeding certified Boolean clauses into integer reasoning

[Implementation](../src/pnp_lab/integer_feedback.py) ·
[checker and adversarial tests](../tests/test_integer_feedback.py) ·
[existing integer certificate format](integer_hull.md).

The input is only a 3-CNF with signed, one-based variable identifiers. The
refuter described here, `integer_feedback_refute`, produces either a proof that the **original** input is UNSAT or
`UNKNOWN`. Its intermediate formula contains checkable Boolean consequences;
in general it is a relaxation. A satisfying assignment of that formula is not
a witness for the original CNF. The [companion witness procedure](../src/pnp_lab/feedback_witness.py)
attempts to construct and check an original Boolean model separately.

## The learning rule

A binary source clause `(p,q)` supplies the implications `-p -> q` and
`-q -> p`. If a clause `C ∨ l` and a path `l -> ... -> t` are available,
then `C ∨ t` follows: when no literal in `C` holds, the raw premise makes
`l` true and the cited binary clauses propagate that truth to `t`.
The rule can retain an actual forbidden Boolean pattern even when the
integer affine hull of each individual premise contains every integer point.
This is ordinary Boolean implication/resolution followed by an integer
consequence, with no claim of a new proof system.

The discovery heuristic is fixed, independent of fixture metadata:

1. Treat as **anchors** the variables occurring in at least two distinct
   signed, proper ternary clauses. Permuted duplicate literals/clauses
   cannot increase the count.
2. Keep non-tautological raw clauses whose coordinates are all anchors.
   For a proper ternary premise with exactly one non-anchor literal `l`,
   group the pair of other literals and source index under `l`.
3. Run one breadth-first search per distinct starting literal through raw
   proper binary clauses. Stop a branch when it first reaches an anchor
   variable (either sign). A reached literal `t` supplies a candidate for
   each associated premise. Skip tautologies and duplicate conclusions;
   keep one path of original binary clauses for each retained conclusion.
4. Keep the learned clauses and their source proofs. Profile their
   individual variable supports: four different forbidden patterns on one
   triple may together impose a parity law even if each pattern, considered
   alone, gives no linear law. The integer phase uses these accumulated
   clauses; it does not replace each newly learned clause immediately with
   its affine hull.

A path is directed. Following only one direction can suffice; equality or
membership in a nontrivial strongly connected component is not required. The
[previous equivalence recovery](blind_recovery.md) uses that stronger condition
because it substitutes variables in the entire formula. Here a one-way path
justifies **adding a consequence**. We never identify its endpoints.

## Arithmetic and original-input replay

There are three distinct ways to propose the final weighted-sum certificate:

* **Parity sum.** Enumerate the eight assignments at each projected ternary
  support, using the projected triples on exactly that support. If the
  permitted four words are precisely a parity half-cube, obtain
  `x + y + z = b (mod 2)`. Sum *all* such rows, with weights one. If every
  coefficient is even and the RHS is odd, the proof is complete. There is
  no graph, designated vertex, charge bit, or elimination order among the
  inputs. Failing this particular sum need not mean the parity subsystem is
  consistent: a contradictory subset may have been missed.
* **Signed column.** The [one-column finder](../src/pnp_lab/one_column_feedback.py)
  searches three-word tables for exact integer laws with coefficients ±1.
  It attempts signed row weights canceling every column except one, then
  checks whether the remaining coefficient divides the RHS. The solver
  records its independent resource statistics when this probe runs.
* **Integer hull.** Otherwise use the existing integer solver on the
  projected clauses. Its table scopes here are exactly those occurring as
  projected clause supports (at most three coordinates each). A feasible
  integer relaxation, a skipped search, or an exhausted cap cannot prove SAT.

The `binary-path-integer-feedback-v1` certificate specifies the original
variable bound, a list of lemma nodes and an ordinary integer-hull proof.
Each node names a zero-based raw source index. For a lifted clause it also
names its starting literal and a list of **signed one-based** binary clause
indices. On binary clause `i=(p,q)` as originally presented, `+(i+1)`
means `-p -> q`, and `-(i+1)` means `-q -> p`. This convention represents
both directions even for original row zero. Reordering an input without
updating the proof generally invalidates its indices.

`replay_feedback_lemmas` validates source membership and each path edge in
order, then verifies the claimed output literals against the reconstructed
consequence. The independent checker does **not** run anchor discovery, BFS,
the parity scan, signed-column search, Smith reduction or general elimination.
It passes the exact reconstructed list, in certificate order, to
`check_integer_hull`. The integer proof's *clause* indices address this
list; its *variable* indices are always the original signed-CNF coordinates
(positive labels for rows, with signs represented by coefficients).
The checker enforces width ≤3 on those local proof scopes. For each term
the old verifier re-evaluates the cited clauses on their local truth table
and verifies its integer law. It then checks that the weighted coefficients
cancel in the claimed modulus and the RHS does not. Thus any original model
would satisfy every derived clause and every cited row and could not yield
that contradiction. Validity never depends on trusting a proposed anchor,
an inferred variable correspondence, or an external SAT answer.

## Discovery and proof cost

Let `m` count raw clauses, `v` occurring variables, `a` anchors, `r`
eligible ternary premises and `b` distinct starting literals. Write `e`
for the number of binary arcs after deduplication, `k` for retained clauses,
and `P` for total path lengths written into the proof. Then

* `v ≤ 3m`, `a ≤ v`, `b ≤ r ≤ m`, and `e ≤ 2m`;
* BFS takes at most `b(2v+e)` vertex/edge visits, with at most `2ar`
  terminal/premise combinations. This counts even unsuccessful searches;
* `k ≤ m+2ar` and `P ≤ 2v · 2ar`: a BFS path cannot repeat a signed
  vertex. Explicitly writing the paths, not just finding reachable pairs,
  is charged. Reconstruction of duplicate conclusions does not copy paths;
* the graph, proof and one live search tree occupy
  `O(m+v+k+P)` integer slots, in addition to the explicit raw input.
  Sorting the projected clauses adds `O(k log(k+1))` comparisons of
  tuples with at most three entries. Indices cost `O(log(m+1))` bits;
  variable labels cost their actual bit length. No arrays indexed by the
  *declared* largest variable name are allocated.

These count combinatorial operations, not unit-time operations on
arbitrarily long integers. Even if hash-table accesses are conservatively
charged a linear scan in the stored keys, these bounds give polynomial
total bit cost for the **learning phase** in the explicit input length.
The copy of the input, all discovery visits, materialized path references
and the independent final replay are part of the algorithm.

The parity scan examines eight words per distinct projected ternary support.
Each has at most eight distinct signed triples. Its sum uses only Boolean
incidence toggles and parity bits; the final checker takes polynomial work on
the displayed proof, with accumulated integer column sums using at most
`O(log(k+1))` bits for these unit-weight terms. Thus when this method
recognizes odd-charge cubic parity blocks, the **complete successful
computation**, including learning, sum discovery and replay, is polynomial;
no worst-case assumption on general integer diagonalization is involved.
This is a conditional algorithmic bound, not a polynomial 3SAT decider.

`max_edges` bounds BFS edge visits, `max_lemmas` counts raw and derived
projected clauses, and `max_path_steps` counts total materialized path
references. Set one to `None` to remove that limit; the structural bounds
above still apply. If a learning cap is reached, the projection is discarded
and the solver returns `UNKNOWN`. The checker has separate lemma/path caps.
The fallback accepts the existing integer limits; `max_bits` also controls
the signed-column probe. Supplying an integer limit other than `max_bits`
skips the signed-column probe. The parity shortcut has its own bounded
eight-word scans and does not run the capped integer eliminator.
`use_parity_sum=False` and/or `use_signed_column=False` disable the
respective shortcuts. Budget metadata is not a proof. Bit complexity and
completeness for the **general uncapped fallback on every input** have not
been established by this work.

## A whole NP-complete presentation on which this feedback remains silent

Suppose every raw clause is a proper ternary clause and no two have the
same unsigned support. There are no binary arcs, so no path lemmas can be
learned. The only remaining clauses are a subset of those same raw triples.
On any selected three-variable support, at most one of them occurs, with
seven permitted words. Neither a four-word parity half-cube nor a
three-word signed-column relation occurs. Moreover the integer affine
lattice of these seven words is all of the integer cube's ambient lattice:
for each coordinate there is an edge in this set along which only that
coordinate changes. Its difference is a unit basis vector. No nontrivial
integer equation or congruence is available, and all three phases report
`UNKNOWN` without needing any budget cutoff.

The obstruction also holds for **any certificate accepted by the specified
checker**, not just for its discovery procedure. Without a raw binary clause
a nonempty path cannot pass replay, so every usable lemma is an original
triple. A local term citing any of these triples must contain all three of
its variables. At width at most three, its cited constraints are thus
either empty or repetitions of just one original clause. Both possible
relations have full integer affine lattice. Every valid local equality or
congruence therefore holds on every integer vector; a weighted contradiction
from such rows cannot exist. This excludes arbitrary proof proposals even
if all anchors and discovery limits are ignored.

The [simple-support reduction](split_parity.md) already embeds general
3SAT into exactly this class. The reduction and decision preservation are
given there; the engine tests independently enumerate one satisfiable and
one unsatisfiable small image. Hence the present **specified one-pass
hybrid**, including both shortcuts and the support-only integer fallback,
does not separate SAT from UNSAT even on an NP-complete image. The obstruction
does not apply to a different gate detector, wider local tables, arbitrary
resolution learning, or all combinations of nonlinear and integer inference.
