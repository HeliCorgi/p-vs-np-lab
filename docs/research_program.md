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
