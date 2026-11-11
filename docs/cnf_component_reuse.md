# Sharing exact residual subproblems across backtracking and counterexamples

Date: 2026-11-11 JST. Status: an implemented exact sharing mechanism and an
amortized cost bound in the number of distinct residual problems. That number
is **not proved polynomial** on general MCSP or SAT inputs.

Research decision, 2026-11-11: the user authorized stopping the broader
extractor-optimization route as the main P-versus-NP proof route. This
implementation and audit are retained as completed work; see the
[current decision](research_program.md#current-decision-stop-the-extractor-optimization-route-2026-11-11).

The [previous fixed constraint representation](mcsp_fixed_constraints.md)
bounded formula size and monotone evidence updates. Extraction still revisited
combinations under different temporary assignments. This continuation makes
one way of avoiding that repeated work explicit: solve a remaining constraint
problem once, and transport its answer to identical remaining problems.
Independent components are solved separately and their models are combined.
The implementation is [cnf_component_cache.py](../src/pnp_lab/cnf_component_cache.py).

## The shared object includes every remaining condition

For an assignment a, first form the exact residual CNF F restricted by a:
delete satisfied clauses and remove falsified literals from the others.
Remove tautologies and duplicate clauses/literals. List surviving variables
in increasing order, rename them to 1,...,q, and sort the resulting clauses.
This whole normalized formula is the cache key. Python dictionary equality
compares the complete tuples; an unchecked hash collision cannot identify
two different problems.

This normalization is a sufficient syntactic equivalence test. It does not
recognize every variable permutation or every logical equivalence, and it
does not invoke a hard equivalence oracle. Its own scans, key construction,
lookups and storage are included in the ledger.

**Renaming lemma.** If the normalized residuals of two contexts agree, their
surviving variables are connected by an explicit bijection preserving every
literal and clause. A satisfying assignment transfers along that bijection;
unsatisfiability transfers in the same way. Therefore the cache can store
either an actual model or a completed NO answer. On a hit, the model is
mapped back to the caller's variables.

The temporary assignment and all retained counterexamples have already been
applied to the formula before its key is constructed. A newly added
counterexample may change that key. An old answer is reused only if the
remaining formula still matches; merely having the same decision prefix
or the same number of constraints is insufficient. Both YES and NO reuse
are tested under changing assumptions.

## Independent components and complete search

Build connected components of the residual variable/constraint graph. If
the formula is F_1 AND ... AND F_k on pairwise disjoint variable sets, it is
satisfiable exactly when every component is satisfiable. Their models can
be united because their domains do not overlap. One unsatisfiable component
proves the conjunction unsatisfiable. A clause connecting two sets of
variables keeps them in the same component.

After unit propagation, the solver either uses this factorization or branches
on a variable. In the MCSP adapter, circuit metadata proposes an order that
visits selectors reachable from the output first. A proposed multiway branch
is used only when its alternatives form an actual positive clause of the
residual formula. Every satisfying assignment must make at least one of
these alternatives true, so the branches cover all solutions. Metadata
changes the order of search; it cannot introduce an unsupported constraint.

Each recursive edge reduces the number of surviving variables: a split
chooses a proper component, or a branch assigns a surviving variable.
Induction proves finite search completeness, unit-propagation correctness,
model transport and component composition. A finished model is also checked
against the original query's clauses and is decoded into an ordinary circuit.
The outer loop verifies that circuit on the complete truth table.

Only completed subproblems are inserted into the table. Work or recursion
exhaustion yields UNKNOWN. Completed descendants remain valid and may be
reused, but an unfinished parent is never recorded as NO. A storage cap
disables new insertions when full; ordinary search continues. Lack of cache
space is not evidence of infeasibility.

This is a use of standard component decomposition, residual-CNF normalization
and memoization. It is not claimed as a new SAT technique.

## A total-work bound, including identifying and building shared problems

Fix a base formula with V variables and literal/clause storage L, and consider
J queries under different assignments, as in counterexample refinement.
Let U be the number of distinct normalized residuals reached. Assume for this
bound that queries finish and the table retains every completed entry.

Each keyed subproblem is expanded at most once. An active computation cannot call itself
through a descendant because the variable count strictly decreases. After
its first completion the table prevents another expansion. Each computed
key creates at most V component or branch calls; the J initial queries add
J more calls. Every restriction, normalization, decomposition, heuristic,
key comparison, model transport and table insertion costs polynomial work
in V,L, including the bit size of indices. Consequently the total has the
form

\[
T\le (U+J)\operatorname{poly}(V,L).
\]

For arbitrarily many generic queries in a bit-cost model, include log(J+2)
in the polynomial to account for query indices. In the MCSP application
J<=N+1 and V>=N, so that factor is already covered by the displayed bound.

This charges incoming cache hits too: recognizing an already solved problem
is not free. For the MCSP pipeline, add construction of the universal-circuit
formula, the previously bounded evidence updates and the full truth-table
verification of each candidate. There are at most N+1 queries in one complete
counterexample run. If U had a uniform polynomial bound in the input size,
these costs would give a polynomial algorithm. **No such general bound on U
has been established.**

An unlimited table may itself occupy O(U(L+V)) logical cells. The measured
implementation caps retained storage at 250,000 cells, counting clause
headers, literal slots, answer metadata and model values. This is not a byte
measurement. Recursive working formulas and contexts consume additional
polynomial stack space. With capped storage, the once-per-key statement is
conditional on no skipped insertions; without it, forgotten subproblems
can be recomputed. With capped work, started but unfinished states are
reported separately from completed ones.

## A constructive case where repeated solving is eliminated

For k independent copies of

\[
H_i=(a_i\lor b_i)\land(\neg a_i\lor b_i),
\]

all components normalize to the same two-variable formula. The first copy
is solved, and its model is transported to the other k-1 copies. For the
specified true-first search and k>=2, only three distinct problems are
completed: the whole conjunction, one copy of H, and its one-variable
residual. The uncached counterpart completes 2k+1 problems.

Reading the k components, identifying them, mapping their answers and
returning a model still costs polynomial work in k. This is a statement
about a fixed repeated component, not polynomial-time solution of arbitrary
components of growing size. It demonstrates the requested reuse without
assuming free preprocessing.

For k=64 the finite run completes **3 problems instead of 129**, with 63
nontrivial cache hits. Including lookup and table costs, its logical work
index is 4,090 versus 5,511. The table contains 532 logical cells. Smaller
examples include cache overhead: at k=2 the indices are 184 versus 179.
The all-k conclusion follows from the decomposition argument, not fitting
these measurements to a growth curve.

## MCSP comparison, including incomplete runs

The [experiment](../experiments/cnf_component_reuse.py) retains all 288 targets
at (n,s)=(2,2),(2,4),(3,3). Both new variants use the same normalization,
component splitting and branching policy; only answer retention changes.
This isolates caching within this new solver. It is not a comparison against
an optimized uncached SAT implementation or a CPU benchmark.

The cap is 500,000 logical work units per extraction in both variants. Costs
include the original constraint construction, permanent updates, all failed
attempts, preprocessing of each query, decoding and candidate verification.
The new ledger differs from the previous extractor's ledger, so their unit
counts are not divided to report a speedup.

| n,s | Uncached YES / NO / UNKNOWN | Shared YES / NO / UNKNOWN |
| --- | --- | --- |
| 2,2 | 14 / 2 / 0 | 14 / 2 / 0 |
| 2,4 | 14 / 0 / 2 | 14 / 0 / 2 |
| 3,3 | 31 / 0 / 225 | 27 / 0 / 229 |

Every definite answer matches the independently enumerated feasible function
set. Every returned intermediate circuit satisfies its retained examples;
final YES circuits match the entire table. UNKNOWN is never counted as NO.

| n,s | Uncached total work index | Shared total work index | Nontrivial hits | Hits from earlier queries |
| --- | ---: | ---: | ---: | ---: |
| 2,2 | 1,910,911 | 1,992,797 | 53 | 23 |
| 2,4 | 8,153,467 | 7,914,487 | 47 | 23 |
| 3,3 | 243,672,396 | 231,699,329 | 1,131 | 406 |

These totals include capped runs. In particular, the smaller three-input
total does **not** establish faster completion: the shared variant completes
fewer targets at the cap and stops earlier in some refinement sequences.
Across the 57 cases where both variants finish, sharing lowers the index on
35 and raises it on 22. There are 231 cases with an unfinished variant;
four finish only without caching. These selected comparisons are not a
success rate on all inputs. Maximum cache occupancy by group is 37,582,
156,843 and 218,842 cells, with no capacity-skipped insertions in this panel.

The [tests](../tests/test_cnf_component_cache.py) separately exhaust all 256
proper two-variable CNFs under all nine partial assignments (2,304 queries),
checking answers by independent Boolean enumeration. They exercise renamed
models, cached NO answers, conflicting new evidence, connected versus
independent constraints, zero cache capacity, timeout recovery, and all
two-input MCSP targets at budget two without an extraction cap.

Full runs are in [cnf_component_reuse.json](../results/cnf_component_reuse.json).

```sh
PYTHONPATH=src:. python -m unittest tests.test_cnf_component_cache -v
PYTHONPATH=src python experiments/cnf_component_reuse.py --out-dir /tmp/cnf-sharing
python scripts/reproduce.py --out-dir /tmp/pnp-reproduced --check
```

## Decision

Retain the earlier circuit-aware extractor as the default. The component
cache is an optional reference implementation for exact reuse, not its
replacement. In the universal-circuit encoding, selector variables occur
across many input rows and tie those rows together. Merely having many rows
does not make them independent. The three-input shared runs perform only
two component splits in total, while identifying residuals has substantial
cost. This explains why the repeated-component guarantee does not transfer
automatically to general circuit synthesis.

Stop treating unrestricted full-residual normalization at every search node
as a demonstrated general acceleration. A further construction would need
either a cheap way to identify useful shared residuals or a bound on the
number of distinct interactions through the shared selectors. Neither has
been proved here. The current result removes repeated expansion when exact
reuse applies and makes its total cost explicit; it does not establish a
general polynomial extraction bound or either answer to P versus NP.
