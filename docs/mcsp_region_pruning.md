# Excluding candidate regions before generating their continuations

Date: 2026-11-11 JST. Status: implemented and checked. This is an exact
finite search with sample-based reductions, not a general polynomial-time
algorithm or a P-versus-NP proof.

The [previous search](mcsp_counterexample_execution.md) saved counterexamples
but still generated a syntactic catalogue independent of them. The new
[implementation](../src/pnp_lab/mcsp_region_search.py) uses those rows inside
candidate generation. It retains one representative for an entire class
of partial circuits, and can prove that a partial circuit has no suitable
completion before producing its children. Both operations have explicit
soundness arguments below. Their computation and every refinement rebuild
are included in the ledger.

## What is excluded

Fix the current examples E=((x_1,t_1),...,(x_k,t_k)). A wire's signature is
its k-bit vector of values on those rows. A search state contains the set S
of signatures of **all available wires**, including constants and inputs.
Let B be the initial set of constant/input signatures and let t be the
target signature. Each transition adds one new signature computed by NOT,
AND or OR. The state represents an ordinary circuit prefix, with parent
links sufficient to reconstruct its gates and sharing.

There are three reductions:

1. If a proposed gate produces a signature already in S, do not generate
   that longer prefix. Its wire can be replaced by an available wire on E.
2. If another prefix has already reached the same set S, do not generate
   the new prefix or its descendants. The retained representative supports
   the same continuations on E with the same remaining gate budget.
3. Before generating children of S, overapproximate all output signatures
   reachable with the remaining gate budget. If t is absent even from that
   relaxation, discard the entire region of continuations.

The first two remove redundant **representations** of sample solutions;
they do not assert that every removed circuit is wrong on the full table.
The third proves that no continuation in that region satisfies E.
In particular, a gate disagreeing with t is not discarded just for that
reason: it may be a necessary intermediate of the correct circuit. The
four-gate XOR test checks this distinction.

## Why the quotient preserves a solution

**Continuation lemma.** Suppose two prefixes have the same available
signature set S. Any sequence of r further gates after the first prefix
can be reproduced after the second on E, using at most r gates. For the
first appended gate, select available wires with the same parent signatures
and apply the same Boolean operation. Its new signature is equal. Repeat
this argument through the sequence. Reuse an existing wire if a result is
already available. This preserves every possible output signature on E.

The generator adds only previously unavailable signatures. A state S thus
uses exactly |S\B| gates in its representative; two representatives of the
same S have equal cost. In an arbitrary prefix, gates whose signatures
duplicate earlier wires can be deleted and all uses redirected, without
increasing cost. Therefore retaining one representative of each S preserves
the existence of a circuit with at most s gates satisfying E. Breadth-first
exploration covers every such signature state unless the separate sound
completion check excludes it. Recording just the output signature, rather
than all available signatures, would not justify this continuation lemma
with the same gate budget and sharing.

**Refinement restores distinctions.** The outer loop starts with no examples,
finds a sample-consistent circuit, and verifies it against the explicit
truth table. A mismatch adds a new row and rebuilds the quotient from the
inputs. A formerly merged pair of wires can now have different signatures;
both possibilities can reappear. No sample-equivalence cut is retained
across this rebuild. Permanently deleting the old representative's rivals
would be unsound.

For example, synthesizing two-input OR produces the full truth tables
0, 15, 10, 14 as successive candidates. Rows 1, 0 and 2 are added in that
order; the candidate that previously looked like the second input is then
replaced by OR. The final circuit is checked on every row.

At most N=2^n distinct rows can be added. Each returned circuit is verified
against the full table. If sample synthesis returns NO, its completeness
shows that even E has no circuit within the budget, hence neither does the
full table. Thus the process terminates in at most N+1 synthesis rounds,
assuming each finite search completes. The expense of a round is not
assumed polynomial. A Python resource failure is not a NO certificate.

## Proving that an entire region has no completion

For r remaining gates define a relaxation on signatures:

\[
R_0=S,\qquad
R_{i+1}=R_i\cup\{\neg a,\ a\land b,\ a\lor b:a,b\in R_i\}.
\]

Here negation is within the k-bit sample mask. Every output of a sequence
of at most i appended gates belongs to R_i, by induction on that sequence.
The relaxation permits unlimited parallel gates per layer, so it may
contain outputs requiring more than i gates. This direction is intentional:
if t is missing from R_r, no allowed completion exists. Finding t in R_r
does not certify the existence of a circuit within r gates.

The implementation caps this relaxation at **128 signature operations per
visited state**. Hitting the cap means UNKNOWN for the exclusion test:
ordinary exploration continues. It never means infeasibility. Any first-layer
gate values already computed are reused during successor generation if the
region survives. All deeper relaxation operations are charged as well.
Setting `relaxation_limit=0` disables only this third reduction; the two
quotient reductions still operate.

An explicit example is XOR with two inputs and a two-gate budget, after
all four rows are known. R_0 has four signatures, R_1 has eight, and R_2
has fourteen, excluding XOR and XNOR. Computing the two closure layers
takes 4(4+2)+8(8+2)=104 signature gate operations. The root is discarded
with **zero child states generated**.

For a precise size of the excluded syntactic region, allow redundant gates,
unordered AND/OR input pairs, and any available output wire. With m wires
there are m(m+2) choices of the next gate. Thus all circuits with zero,
one or two gates have

\[
4+24\cdot5+24\cdot35\cdot6=5,164
\]

descriptions in this convention. All are ruled out by the one root cut.
This is a count of descriptions, not distinct functions, and the 104 vector
operations have width four and additional bookkeeping costs. The claim is
pre-generation exclusion, not a 5,164/104 runtime speedup or a new XOR result.

## Cost, including rebuilding and failed pruning attempts

For k examples there are at most 2^k signatures. Write b=|B|. The number of
possible quotient states is bounded by

\[
Q_k\le\sum_{j=0}^{\min(s,2^k-b)}\binom{2^k-b}{j}.
\]

Only some of these sets are constructible, and search stops at the first
solution. Each expanded state has at most n+2+s available signatures and
O((n+s+2)^2) possible gate operations. Signature operations have width k,
not unit bit cost. With deterministic dictionaries, signature sorting and
witness reconstruction charged, a coarse bit-cost upper bound per round is
`(Q_k+1) poly(k,n,s,L+1)`, for relaxation cap L. The bound includes storing
representatives and their parent links. Full verification costs at most
`O(N(n+s))` logical Boolean operations per candidate, with address costs
added in a bit model. All round costs are summed; restarting is not free.

The ledger records signature bit widths, transition attempts, state-key
entries, all relaxation work, witness construction, input loading and full
verification. It is an accounting index, not exact Python instruction or
wall-clock time. Tuple sorting, dictionary internals and trace serialization
are not individually timed; they are covered only by the coarse cost bound.
Memory includes retained states, representatives, signature keys, the bounded
relaxation workspace, the explicit input and the saved audit traces. The
reported peak state count alone is not total memory in bytes.

The expression for Q_k can still be very large and k can reach N. These
reductions supply no `N poly(n)` upper bound and no lower bound on other
algorithms. They are implementations of standard observational equivalence,
counterexample refinement and abstract reachability; no novelty is claimed.

## Independent audit and comparison

The [experiment](../experiments/mcsp_region_pruning.py) keeps the previous
panel: all truth tables at (n,s)=(2,2),(2,4),(3,3), 288 cases. It runs the
quotient alone and the quotient plus bounded relaxation: 576 searches.
Every final answer agrees with an independent semantic circuit catalogue.
All 2,776 intermediate witnesses agree with their current samples, and
every final YES witness agrees with the whole table.

Each of the **7,096 region cuts** is separately checked by enumerating
literal straight-line suffixes, including duplicate wires. That checker
does not use the depth relaxation. Identical certificates are shared only
when writing the report: 2,157 stored certificates cover the 7,096 cuts.
The synthesis algorithm receives no catalogue or certificate table from
this audit. The [tests](../tests/test_mcsp_region_search.py) also cover every
two-input partial table at budgets zero through two, cap exhaustion,
restored distinctions, and all three-input truth tables at budget two.

The following state counts include all refinements and all targets in each
group. Old states are syntactic; new states are sample signatures, so these
counts are not a common unit of execution time.

| n,s | Previous lazy search: states created | Quotient only | Quotient + region cuts |
| --- | ---: | ---: | ---: |
| 2,2 | 2,758 | 154 | 109 |
| 2,4 | 740,705 | 373 | 232 |
| 3,3 | 6,648,091 | 45,457 | 15,213 |

Within the two new variants, the same accounting index includes pruning
and rebuilding costs:

| n,s | Quotient only: work units | Quotient + region cuts: work units |
| --- | ---: | ---: |
| 2,2 | 6,850 | 7,990 |
| 2,4 | 37,164 | 59,413 |
| 3,3 | 4,279,592 | 5,817,114 |

Adding lookahead creates fewer states on 224 cases and the same number on
64. Its work index is lower on 2, equal on 13, and higher on 273. Maximum
states held per synthesis round fall from 17/127/481 to 7/57/77 across the
three groups. Therefore the extra region check trades work for fewer states
in this panel; fewer generated candidates alone is not a speedup claim.
The quotient is independently available when this lookahead is not worthwhile.
The old search's different cost ledger is retained for reference, without
dividing unlike accounting indices to manufacture a speedup percentage.

Full results, round costs and exclusion certificates are in
[mcsp_region_pruning.json](../results/mcsp_region_pruning.json). Round examples
are encoded as prefixes of each run's final example list. Aggregate ledgers
retain every metric; the per-round display contains the main counters.

```sh
PYTHONPATH=src:. python -m unittest tests.test_mcsp_region_search -v
PYTHONPATH=src python experiments/mcsp_region_pruning.py --out-dir /tmp/mcsp-regions
python scripts/reproduce.py --out-dir /tmp/pnp-reproduced --check
```

The requested pre-generation reduction is now concrete and has a completeness
argument. Remaining work on execution cost must control the growth of the
sample-state space or make its exclusion cheaper. This investigation does
not establish a universal lower bound against future algorithms, a general
polynomial synthesis algorithm, or either answer to P versus NP.

The [fixed-constraint continuation](mcsp_fixed_constraints.md) removes formula
growth and proves polynomial total evidence propagation using a universal
circuit encoding. Extraction is implemented with polynomial space and
explicitly measured search cost; its general polynomial-time bound remains
unproved.
