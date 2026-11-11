# Explicit circuit synthesis with counterexamples and shared evaluation

Date: 2026-11-11 JST. Status: implemented finite exact search, with proved
reuse bounds. No general polynomial bound, new circuit lower bound, or
P-versus-NP conclusion is claimed.

The [previous construction](mcsp_merge_reconstruction.md) made witness
selection uniform but left prefix feasibility as an oracle. Here we take
a concrete step on execution cost: generate ordinary circuits as needed,
retain counterexamples, and reuse evaluations of shared gates. Finding a
witness stops generation immediately. Reporting NO requires exhausting the
complete bounded search. Neither candidate generation nor preprocessing
is supplied as free advice.

This is direct synthesis from a complete truth table. It does **not**
implement the previous predicate on arbitrary prefixes of its fixed circuit
encoding: structural canonicalization changes descriptions. In particular,
the previous oracle-circuit size/depth bounds cannot be transferred to this
sequential program. The common task is finding a small consistent circuit.

## Implemented procedure

Input is an explicit N=2^n-bit truth table T and a gate budget s. The circuit
basis is fan-in-two AND/OR and unary NOT, with constants and input wires
free. Outputs may be any available wire. The output is an ordinary circuit
of at most s gates, or NO for this budget and basis.

1. Generate circuits by increasing numbers of available distinct gates.
   A state records its available gates. Identical operation/parent triples
   share a structural node, and AND/OR parents are put in a canonical order.
   This uses syntax only; it does not evaluate functions to merge candidates.
2. Test each new output root against saved counterexample rows, newest first.
   A failure discards that root. The generator continues from its existing
   position; it does not restart after each counterexample.
3. If the root passes, check the remaining truth-table rows in order. Save
   the first mismatch. If all rows agree, export the reachable circuit DAG
   and stop, without finishing the remaining catalogue.
4. Store each evaluated `(row, structural node)` value. Later candidates
   reuse the same value whenever they contain that node. The target bits
   are also cached after reading the explicit input table.

The implementation is [mcsp_counterexample.py](../src/pnp_lab/mcsp_counterexample.py).
`search_lazy(n, s, T)` returns the generated catalogue and the search result.
The catalogue's `complete` flag distinguishes early success from exhaustion.
An incomplete or truncated root stream cannot certify NO.

Counterexample-guided search, structural hashing, memoization and lazy
enumeration are standard mechanisms. Their combination here is an auditable
implementation, not a claim of a new synthesis technique.

## Correctness for arbitrary finite parameters

**Catalogue completeness.** Delete unused gates and merge structurally
identical gates of any circuit with at most s gates. These operations preserve
the function and cannot increase the number of gates. Order the remaining
gates topologically. Initially all input and constant wires are available.
At each step the generator considers every allowed operation on available
parents, so it can add the next gate. A state can be stored as a set of gate
identifiers: future choices depend only on available gates, not the order
in which they were introduced. Deduplicating these states preserves every
possible continuation. Thus some generated root computes the original
function. Conversely, a new root is created in a state with at most s gates,
so its reachable sub-DAG contains at most s gates. Global sharing of nodes
does not charge other candidates' unrelated nodes to the exported circuit.

**Search correctness.** Every saved example is a row on which an earlier
candidate differs from T. A correct candidate passes every such test. A
candidate is returned only after both saved and remaining rows agree with
T. Export preserves its shared sub-DAG, so the returned circuit is valid.
If all catalogue roots are visited and none passes, completeness proves
that there is no circuit within the stated budget. For partial generation,
failure to find a witness yields no such conclusion; the API rejects that
attempt to return NO. A successfully returned witness needs no completeness
flag. Python resource limits can interrupt a run; interruption is not NO.

**Progress.** A candidate passing the saved examples can fail only at a new
row. Hence at most N distinct counterexamples are stored. The candidate
cursor only advances and each generated root is visited once. This proves
finite termination after complete enumeration, not a polynomial number of
candidate visits. Arbitrarily many roots can fail the same saved example.

## Execution cost and what is actually avoided

Let M be the number of visited roots, G the number of generated shared gate
nodes, and P the actual cost of the generated part of the catalogue. These
are quantities of the run, not assumed polynomial functions of n.

- There are at most NM root/row comparisons. Screening uses distinct saved
  rows; subsequent verification skips them. Each root tests each row at most
  once, although the verification loop also counts its skipped slots.
- Each gate value is computed at most once per row: at most NG gate
  evaluations in total. Each fresh gate evaluation makes at most two child
  calls, so memo lookups are at most NM+2NG. Repeated evaluation of a shared
  subcircuit is thereby removed, rather than merely bounded by its size
  again for every containing candidate.
- At most N(G+n+2) node values and N target bits are cached. This is a time
  and space tradeoff; the cache is not free or polynomial in n.
- Lazy generation visits exactly the same roots and makes exactly the same
  comparisons as eager generation with the same retention mode. It avoids
  the unneeded suffix of catalogue construction on a YES input. On a NO
  input it finishes construction, as required for a sound answer.

Using balanced dictionaries, counters, indices and an explicit stack gives
a deterministic bit-cost implementation with total work bounded by

\[
P + \bigl(N(M+G+n+1)+M+s\bigr)
       \operatorname{poly}(n,s,\log(M+G+2)).
\]

The last polynomial includes address sizes, lookups, row-set membership and
witness export. This is an implementation bound for these operations, not
the exact cost of the Python dictionaries used in the experiment.
Frontier-state storage must be added to the cache: if F states are held,
their keys occupy O(F s log(G+n+2)) bits, and the generated gate graph also
occupies space. Reported frontier and cache counts are numbers of records,
not byte measurements.

The remaining enumerative expense is explicit. At each of at most s steps
there are O((n+s+2)^2) syntactic gate choices. Consequently a complete
enumeration, including its state bookkeeping, has the usual upper bound
`2^{O(s log(n+s+2))}` up to polynomial factors. At s=n² this gives
`2^{O(n² log(n+2))}`, far above the desired `N poly(n)` scale. This is an
upper bound on this construction, not a lower bound on all synthesis
algorithms. Reuse bounds do not imply that P, M or G is small.

## Finite audit, including generation

The [experiment](../experiments/mcsp_counterexample_search.py) fixes all truth
tables for `(n,s)=(2,2),(2,4),(3,3)` and four variants before measurement:

| Variant | Saved examples | Shared values across roots | Generation |
| --- | --- | --- | --- |
| `fresh` | No | No | Full catalogue first |
| `samples` | Yes | No | Full catalogue first |
| `samples_and_gates` | Yes | Yes | Full catalogue first |
| `lazy_samples_and_gates` | Yes | Yes | Stop at first valid witness |

Every variant preserves sharing **within** an individual circuit evaluation.
The target is loaded as an explicit table and charged N input bits. The
generator's order is independent of that table. No target-dependent advice,
truth-function catalogue or feasibility oracle guides the search.

The accounting index sums input bits, candidate visits, sample checks,
verification slots, memo lookups, computed node values, target accesses and
counterexamples. Construction adds attempted transitions, state insertions,
created state records and created roots. Eager generation is charged afresh
for every input even though the audit reuses the catalogue for convenience.
Lazy generation is charged the part actually produced for that input.
These are **logical event counts**, not elapsed seconds or exact bit
operations. Sorting comparisons, tuple-copy lengths, hash-table internals
and witness export are not individually represented in the index; their
costs belong in the bit-cost bound above. Independent audit work is outside
the search index and is not being attributed to the synthesis algorithm.

Aggregates over every truth table in each group, including NO inputs:

| n,s | Tables (YES/NO) | Fresh: generation + search events | Shared values, eager: same index | Shared values, lazy: same index |
| --- | ---: | ---: | ---: | ---: |
| 2,2 | 16 (14/2) | 67,488 | 57,579 | 28,379 |
| 2,4 | 16 (16/0) | 38,865,404 | 36,265,024 | 5,577,029 |
| 3,3 | 256 (84/172) | 91,464,005 | 63,999,320 | 53,266,452 |

The reductions of this index relative to `fresh` are about 58%, 86% and
42% for the lazy variant. They are comparisons to this explicit baseline,
not claims of competitive MCSP performance. They do not estimate P versus
NP. In the search-only index, shared-value retention is worse than `fresh`
on 10 of the 288 cases because the example order and bookkeeping change.
It never increases gate evaluations or the search index relative to
`samples`, which has the identical query order. Adding lazy generation
reduces the combined index on all 288 cases in this finite panel; no
universal dominance over other algorithms is claimed.

The additional space is substantial. Maximum cached node values within a
run are respectively 592, 135,916 and 21,860 for the sharing variants,
versus 5, 8 and 7 for `fresh`. Full generation holds up to 564, 391,490 and
33,810 frontier-state records. All per-input construction and search
counters are stored in the [result](../results/mcsp_counterexample_search.json).

All 1,152 searches are checked against a separately enumerated exact set of
feasible Boolean functions. That audit uses semantic states and is never
called by the search procedure. Every YES witness is interpreted separately;
every NO status agrees with this finite oracle. The lazy and eager sharing
variants have identical witnesses, counterexample sequences and search
counters. [Tests](../tests/test_mcsp_counterexample.py) also exercise circuit
sharing and reject incomplete NO claims. These checks are executable
finite evidence; the arbitrary-parameter arguments above are not Lean proofs.

```sh
PYTHONPATH=src:. python -m unittest tests.test_mcsp_counterexample -v
PYTHONPATH=src:. python experiments/mcsp_counterexample_search.py --out-dir /tmp/mcsp-search
python scripts/reproduce.py --out-dir /tmp/pnp-reproduced --check
```

## Remaining constructive task

**Continuation:** [sample-state region pruning](mcsp_region_pruning.md) now
implements equivalence-class reduction and sound completion-based exclusion
before generating descendants. It includes the required refinement rebuilds,
all pruning costs and independent checks of the discarded regions. The
paragraphs below record the motivation at this earlier stage.

The previous oracle call is no longer needed by this direct search. The
unresolved expense is now located in actual code: generating and screening
many structurally distinct candidates. Retaining the first counterexample
does not remove a whole region of the generator's state space. A next
useful change must do that with a verifiable exclusion invariant, or build
a consistent candidate directly from retained constraints, while charging
its own construction cost. Counting fewer full verification calls alone
will not establish the needed bound.

Keep this procedure as the correctness and cost baseline for such a change.
It does not supply the general circuit lower bound needed by the
McKay–Murray–Williams magnification route. Conversely, even a faster MCSP
upper bound would need a justified reduction before implying P=NP.
Neither direction of the original goal has been proved by this experiment.
