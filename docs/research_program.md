# Research objective and audited starting point

**Goal:** a complete mathematical proof of P=NP or P≠NP. **Status:** open.
The [solution criteria](solution_criteria.md) specify the quantifiers; Clay's
[official listing](https://www.claymath.org/millennium/p-vs-np/) still marks
the problem unsolved (checked 2026-11-05 JST). The repository is a research
record. Its phase numbers measure completed investigations, not proximity
to a Millennium Prize solution.

## Starting audit for this cycle

The GitHub main reference was
[`6e34ce5`](https://github.com/HeliCorgi/p-vs-np-lab/commit/6e34ce5b3e98bc12c72c3916ea6bca0aa1a8cb05).
We inspected all 38 commit subjects on its main ancestry, the README and
research decisions, representative formal proofs, implementations, reports,
and failure records. All 409 base file blobs matched the GitHub tree before
editing. This is a scope-and-provenance audit, not an independent proof of
every assertion previously committed.

| Research phase | What remains useful | What stopped the argument |
|---|---|---|
| 1–4: boundary compression, XOR, and counting | Exact composition under explicit hypotheses; a reduction reaching general 3-SAT; witnesses and finite checks. [First claim ledger](research_notes.md) | Some chosen boundary representations need exponential size; quotient enumeration still has an exponential parameter. A correct decomposition on examples is not a uniform bound. |
| 5–10: small blocks, sparse choices, affine holes | Tractable fragments, explicit reductions and obstruction families. [Decisions and older baselines](reverse_engineering.md) | Sparse representation still encodes general SAT. A small local table or shorter certificate does not bound total discovery or composition. |
| 11–13: pruning and model transport | Precise target for reducing branch counts; transport and recovery on specified encodings. [Resolution barrier](layered_resolution_barrier.md) | Specific labels or resolution-justified substitutions require too many distinct states or large proofs. These are not lower bounds on arbitrary algorithms. |
| 14–15: modular and integer structure | Original-input certificates for hidden flow and prime-power obstructions. [Integer limits](global_integer_theory.md) | Even all raw affine laws on the allowed scopes can be trivial; singleton tests need not help. The [old recovery](modular_padding.md) depends on private pivots or other recognizable structure. |
| 16: preserve nonlinear relations | Exact finite thresholds on the 31-variable core, checked traces, and a proper-linear-3-CNF family hard for polynomial calculus over every field. [Proof boundaries](correlation_proof_boundary.md) | Bounded resolution width or PC degree is not complete; the preceding all-field lower bound did not by itself cover a system using additional integer lemmas. |

The starting [CI run](https://github.com/HeliCorgi/p-vs-np-lab/actions/runs/41819485348)
passed 341 tests, reproduction of 48 deterministic reports including the
summary, and 70 Lean theorem dependency audits. The independent 180-minute
[`openai/math` upstream attempt](../results/upstream_math_audit.json)
recorded a failed job without a verified terminal theorem/axiom result.
This is neither rejection of the upstream theorem nor a successful local
rebuild. Even the stated subexponential bound would not supply a polynomial
one. We retained the pinned sources and their integrity checks, without
restarting the expensive unfinished audit.

## Phase 22: Boolean restriction dimension (2026-11-06 JST)

Starting main was `42e2dde0d32bd19a4fdce4b701d3b1f5525906a1`.
All 511 file blobs matched the local tree, recent history and open PRs (none)
were checked, and both main workflows had succeeded. The preceding proof
modules, explicit scope boundaries, and next acceptance test were read before
choosing this cycle's target.

The [new restriction proof](boolean_restriction_dimension.md) constructs
linear maps into actual Boolean function spaces, proves their kernel meaning,
and proves their image dimensions are at most the explicit truncated binomial
sum. A clause-level adapter connects raw initial polynomials and compressed
derived polynomials to the existing semantic DAG replay. The composed theorem
therefore proves its numerical image budgets internally. Supplied affine
parameterizations and coverage remain explicit data; optimal intrinsic
dimension is not assumed.

The four new modules compiled on their first hosted attempt. Thirty new theorem
endpoints extend the ordinary-PC axiom audit from 38 to 68; only standard
logical axioms were observed. The [new audit record](../results/boolean_restriction_formal_audit.json)
preserves exact sources and CI evidence. A focused independent internal
statement audit found no coverage-direction or hidden-conclusion defect and
confirmed that all tagged input clauses have the stated raw width bound.
No new upstream source files or finite benchmark reports were added.

The next target is a bijective affine parameterization of each nonempty clause
zero-set with exactly `n - spanRank C` parameters, followed by the expander
separator and quantitative proof. The full exponential bound remains a paper
proof with incomplete formalization and no external specialist review. No
P versus NP resolution or general polynomial-time SAT algorithm was obtained.

## Phase 21: ordinary-PC formalization cycle (2026-11-05 UTC)

Starting main was `08ab7b79d1537b444a42bbec4d374e24090aae70`.
All 491 file blobs matched the local snapshot; the current README, research
decisions, phase-20 proofs and failure controls, recent commits, open PRs
(none), and successful main CI were checked. The selected task was the exact
first gate left in phase 20: formalize the ordinary-PC replay, rather than
increase the finite benchmark sizes.

The [phase-21 package](ordinary_pc_formalization.md) contains actual ordinary
polynomials and primitive degree-bounded PC derivations, a complete weighted
semantic-DAG replay, concrete basis-compressed affine indicators, and a
connected dimension-budget theorem. Its hosted Lean build and transitive axiom
audit passed, with 38 named theorem audits allowing only standard logical
axioms. The [source/CI record](../results/ordinary_pc_formal_audit.json) preserves
the actual result separately from Python reproduction. The geometric restriction image
and expander separator remain explicit missing bridges to full formalization
of the exponential lower bound.

Three unmodified MIT-licensed foundation files by Kamil Braun are reused with
full attribution, pinned hashes, and license notices. Their first hosted build
succeeded. The initial lab modules exposed elaboration issues (a comment
delimiter, universe/decidability inference, explicit zero/one cases, and a
dimension rewrite). A later literal-injectivity timeout was resolved by typed
equalities without changing the theorem or raising heartbeat limits. These
failed checkpoints are followed by the successful complete package build and
axiom audit. No mathematical counterexample to the replay
argument was found in this bounded audit. Selective compilation does not
certify the upstream bit-PHP theorem. The old `openai/math` snapshot and its
failed 180-minute audit record are preserved without relaunching that build.

The [next acceptance test](reverse_engineering.md) is the actual Boolean
restriction map with its squarefree dimension, followed by the published
graph-reduction interface. The [general lower-bound register](strong_lower_bounds.md)
preserves the phase-20 paper theorem with its current evidence level. No
all-algorithm lower bound or polynomial-time general SAT algorithm has been
obtained.

## Phase 20: dated outcome (2026-11-05 UTC)

Starting main was `c6a2b2e758c618c355149b70fc24437c470db145`.
Its 474 file blobs matched the local tree before editing. Recent history,
open PRs (none), and successful head CI runs were checked. This cycle took
the preceding separated-space question seriously rather than relabeling
the earlier PC refutation-degree bound.

The [direct common-annihilator theorem](affine_dag_annihilator.md) bounds
semantic unary/binary affine-clause DAGs by a low-degree separated-space
dimension. The [expander construction](expander_separated_space.md)
supplies such a space and a fixed occurrence bound, leading to an
exponential node-count bound, and even an exponential count of distinct
high-rank falsity flats, on an existential proper linear 3-CNF family.
Arbitrary sharing, depth, and parity support are allowed. The source lines
remain affine clauses on the original F2 variables. This paper argument
was independently examined within the cycle; complete formalization,
external review, and any priority assessment remain outstanding.

The [upstream source audit](braun_generic_audit.md) read and hash-verified
17 additional pinned Lean files. No upstream build was run. The new
direct proof removes the registry/removal theorem from this lab result's
dependencies; the published Mikša–Nordström graph-reduction theorem remains
an explicit mathematical input.

Three new reproducible reports audit actual PC consequence spaces,
masked DAG-to-PC traces, and support/parameter counts. Failure controls
separate static from dynamic polynomial consequences and individual
nonmembership from independence of a span. The Lean addition verifies
six semantic and budget lemmas, not the complete lower-bound theorem.
This is a strong proof-system result recorded independently of the ultimate
goal. No polynomial-time general SAT algorithm, all-algorithm lower bound,
or P versus NP resolution has been obtained.

## Phase 19: dated outcome (2026-11-05 JST)

Starting main was `8bfca4c451d6be1cbc84be50f9d6f667f66528a3`.
All 455 file blobs matched its recursive Git tree before editing; recent
commits, open PRs (none), and completed CI runs were checked. The cycle
addressed parity queries, the specific next gate left in phase 18.

The [general expansion theorem](parity_localization.md) now covers short
parity questions with arbitrary-modulus integer terminals. A complementary
[same-field theorem](parity_pc_bridge.md) covers arbitrarily wide parity
queries with bounded-degree ordinary-PC terminals, including heterogeneous
degree budgets. Both are tree results, with all restrictions stated. The
[strong lower-bound record](strong_lower_bounds.md) retains these reusable
statements and attributes established results separately.

The new finite artifacts audit both-answer extension, a rank-charge
counterexample, original-clause parity certificates, and legal ordinary-PC
branch discharge and composition. The simple parity-block positive class
has a proof-discovery and bit-cost argument, not just a short supplied proof.
The [primary literature map](parity_query_prior_work.md) also records a
September/November 2026 unrestricted-DAG claim. Its
[bounded semantic source review](braun_resoplus_audit.md) does not certify
the entire external formalization, and it is not a premise of the lab's
new proofs. No all-input SAT algorithm, general algorithmic lower bound,
or P versus NP solution candidate was obtained.

## Phase 18: dated outcome (2026-11-05 JST)

The new [support theorem](support_localization.md) answers the previous
high-digit question negatively on the lab's existing all-field-hard
expander family. Even [trees of variable queries with integer refutation
leaves](conditional_localization.md) have an exponential leaf lower bound
there at fixed width and local scope. A separate [Boolean field-switch
family](field_split_boundary.md) admits polynomially discovered mixed-field
proofs with one split, yet its [unpinned integer relaxation](coprime_pseudomarginals.md)
survives every modulus. This is consistent with published two-prime CSP
constructions; it is not an all-input lower or upper bound. The new
[acceptance test](reverse_engineering.md) concerns rules genuinely outside
the variable-tree model such as wide parity queries or certified branch
sharing. The ongoing objective and standard for a solution remain unchanged.

## Phase 17: question, evidence, and stopping decision

**Falsifiable question.** Can independently justified nonlinear clauses
enable global arithmetic on a whole family where the raw integer stage
is blind, the previous private-variable rule cannot start, and ordinary
resolution alone is provably expensive? Exclude a mere increase in caps.
Require an original SAT word or replayable UNSAT proof, account for finding
it, and identify an input class on which this feedback still fails.

- **Paper proofs:** [signed implication shields and both-side family decision](feedback_separation.md);
  [composite carry recovery](feedback_carry.md); [degree simulation of one final integer sum](feedback_simulation.md).
- **Executable evidence:** [parity and failure controls](../results/integer_feedback.json),
  [prime powers](../results/feedback_prime_power.json), [first-digit coefficients](../results/feedback_simulation.json),
  [higher-digit identities](../results/feedback_digits.json). Finite identity checks are not the uniform degree proof.
- **Lean scope:** [binary edges, path composition, replacement in a disjunction, and sound transport of an integer refutation](../Formal/IntegerFeedback.lean).
  The quantitative separation, degree simulation and Python code are not formalized here.
- **Negative result:** the front end can recover the *entire* source formula
  on an NP-complete class yet produce no local integer information. Neither
  more examples of the same shields nor larger fixed local tables answers this.

**Next acceptance test.** On the prior all-field-hard family, small learned
clause width and small integer scopes would require a genuinely high
detecting digit in every successful one-sum proof. Seek a family and an
algorithm with independently justified hardness for the comparison system,
polynomially discoverable arithmetic certificates, and an accounted total
bit cost. Rule out trivial rescaling and low-width explanations. If that
route fails, publish the precise obstruction or switch to a different proof
language; do not silently assume the new language inherits old bounds.

Each future cycle starts from current main and unfinished work, states a
testable hypothesis, and stops on a verifiable advance or a documented
failure. An apparent all-input solution triggers independent adversarial
review and a **candidate** notice. Finite measurements, a restricted family
theorem, bounds for a chosen proof system, or a successful Lean build alone
do not trigger a solution announcement.
