# Phase 29: generic identical-circuit miter as an adversarial charging test

Date: 2026-11-10 JST. Preregistered against main `a39c8a1be8e8082d150e92f00a546dacd7379034`.

## Starting status and nonduplication

Read main README, `docs/reverse_engineering.md`, Phase 28's `docs/tseitin_resolution_miter.md`, recent main commits, branches, open issues/PRs and Actions. PR #7 (`research/physical-sat-bridge`) is open, green on its current head and includes substantial Phase-20 formalization, physical SAT, CDCL, circuit extensions and hierarchy/circuit audit. This cycle **does not modify PR #7**, its studies, its reported measurements, the previous inner-product cover search, or the existing Lean files. Earlier Phase 28 proved a *specific* inner-product two-copy miter has a linear width-three ordinary-resolution proof. The new test generalizes the proof template to arbitrary explicit mixed-gate DAG circuits and checks what it does **not** say.

## Preselected hypothesis and falsifiers (before implementation)

**H:** Let C be a single-output, topologically ordered acyclic Boolean circuit on n >= 2 primary inputs, with g >= 1 distinct output wires and fan-in at most 2, gates in {AND, OR, XOR, NOT}. Each binary gate has syntactically distinct input wires. Gate outputs are fresh; edges may share predecessors arbitrarily. Build two *syntactically identical* definitional Tseitin encodings with shared primary input variables, separately named gates, and opposite output units. Then their conjunction is UNSAT and has a **DAG ordinary-resolution refutation** with at most

    8 * (#AND + #OR) + 14 * (#XOR) + 4 * (#NOT) + 2

derived lines and width at most 3. Only original Tseitin gate clauses and the two output units are input axioms; every derived line has exactly two earlier parents and a resolved literal. No weakening, semantic rule, gate-equivalence axiom, or extension rule. The number of input clauses is exactly 6 * (#AND + #OR) + 8 * (#XOR) + 4 * (#NOT) + 2, counting the two copies and final units, and total variables are n + 2g.

**Falsifiers:** A syntactically invalid or widened (width > 3) derived line, a nonempty final clause, incorrect input count, counterexample to miter UNSAT, a failing bounded independent checker, or a gate/fanout/order case with more lines than the formula. Repeated operands, unknown gates, forward wires and absent gate outputs violate *declared preconditions* and must be rejected; they are not searched for a hidden proof.

**Hard cutoff:** Use deterministic DAG examples and five fixed random seeds, at most 12 gates; raw exhaustive Boolean semantics only when n + 2g <= 10 (at most 1024 assignments per input), with non-vacuous same-output sibling controls. Build a separate signed-literal-set checker not invoking the proof generator's resolution routine. Modify a pivot, parent, clause, or source input in negative controls and ensure rejection. No heavy SAT solver, no unbounded search, no larger affine flat enumeration, no Lean theorem claimed. Stop upon any invalid inference, rather than silently weakening the claim.

**What the test would and would not establish:** This extends Phase 28's *counterexample to unqualified charging* from one structured function to arbitrary circuits' identical-copy miters. It does not refute a lower bound for a genuinely different hard unsatisfiable family, asymmetric equivalence check, general circuit equivalence, or any algorithm for SAT. In particular, the miter is guaranteed unsatisfiable by construction, so its short proof is not a general unsatisfiability algorithm.

## Primary literature read

- S. A. Cook and R. A. Reckhow, *The Relative Efficiency of Propositional Proof Systems*, JSL 44(1):36–50 (1979), DOI [10.2307/2273702](https://doi.org/10.2307/2273702). Author manuscript: https://www.cs.toronto.edu/~sacook/homepage/cook_reckhow.pdf . Framework for syntactic, efficiently checkable proof systems; not a source asserting the exact new line count.
- G. S. Tseitin, *On the Complexity of Derivation in Propositional Calculus* (1968; reprinted in *Automation of Reasoning*, 1983), DOI [10.1007/978-3-642-81955-1_28](https://doi.org/10.1007/978-3-642-81955-1_28). Background for proof complexity and Tseitin encodings; not a claim that he proved this specific miter template.

## Outcome

Pending the above bounded tests and independent certificate replay. Mathematical scope is a constructive paper derivation; implementation tests are finite. No new Lean verification is planned.
