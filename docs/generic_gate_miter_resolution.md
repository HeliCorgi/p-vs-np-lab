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

## Mathematical proof: all admissible circuits

**Theorem.** The preselected bound holds for every admissible circuit, not only the finite examples. For each original wire (u), write (u_A,u_B) for its representation in the two copies (the exact same variable if (u) is primary). Use the invariant: for all completed gates, the proof already contains both binary clauses ((\neg u_A\lor u_B)) and ((u_A\lor\neg u_B)). Primary-input identity needs no clauses.

**Transport of a B-copy predecessor literal.** For positive (u_B), resolve with ((\neg u_B\lor u_A)) to replace the literal by (u_A); for negative (\neg u_B), resolve with ((u_B\lor\neg u_A)) to replace it by (\neg u_A). Every such replacement uses exactly one ordinary resolution step and preserves width. A primary input needs no replacement. Distinct binary gate operands ensure that no unintended duplicate or complementary predecessor literal occurs.

**Gate templates and step counts.** Let (a,b) be the A-copy predecessors of a binary gate, (p) its A-output and (q) the corresponding B-output. Prime B-copy predecessor literals are first transported to (a,b), using earlier invariants.

* AND: A has ((\neg p\lor a),(\neg p\lor b),(p\lor\neg a\lor\neg b)); B has the analogous three clauses for (q). Transport the two predecessors in B's long clause (at most 2 resolutions). Resolve with A's first and second short clauses (2 resolutions) to obtain ((\neg p\lor q)). Transport the predecessor in each of B's two short clauses (at most 2 more resolutions). Resolve those against A's long clause (2 resolutions) to derive ((p\lor\neg q)). Total at most 8.
* OR: A has ((p\lor\neg a),(p\lor\neg b),(\neg p\lor a\lor b)); B is analogous. Transport B's two short clauses (at most 2), resolve against A's long clause (2) for ((\neg p\lor q)). Transport B's long clause (at most 2), resolve against A's two short clauses (2) for ((p\lor\neg q)). Total at most 8.
* NOT: A has ((p\lor a),(\neg p\lor\neg a)); B has the analogous two clauses. Transport the lone predecessor in each B clause (at most 2) and resolve once for each of ((\neg p\lor q)) and ((p\lor\neg q)). Total at most 4.
* XOR: Enumerate its four clauses as (A_0=(a\lor b\lor\neg p)), (A_1=(a\lor\neg b\lor p)), (A_2=(\neg a\lor b\lor p)), (A_3=(\neg a\lor\neg b\lor\neg p)). Transport both B predecessors in all four clauses (at most 8), giving (B_i) with A predecessors but B output (q). Resolve (A_0,B_1) on (b), and (B_2,A_3) on (b); the two results have opposite (a) literals and resolve to ((\neg p\lor q)). Likewise (B_0,A_1) and (A_2,B_3) resolve on (b), then on (a) to ((p\lor\neg q)). Six further resolutions; total at most 14.

Every intermediate resolvent has at most three literals. All gate copies have fresh outputs, so a gate is handled only after its input equalities have been derived. Reusing those binary clauses is legal in a **DAG** resolution proof; a tree-like proof is not claimed. Induction in topological order establishes both output implications for every gate. Finally the positive A-output unit resolves with ((\neg p\lor q)) to give ((q)), and that unit resolves with the negative B-output unit to give the empty clause. This is 2 further resolutions. No rule other than ordinary binary resolution is needed.

The Tseitin gate clauses force both circuit copies to compute the identical Boolean function from shared primary inputs; opposite final units therefore make the formula UNSAT. There are (n+2g) distinct variables and exactly the preselected number of input clauses. By summing the per-gate templates and final two resolutions the derived-line bound follows. **This is a mathematical proof about specified syntactically identical circuits**, not a lower bound, a general circuit-equivalence algorithm, or a P-versus-NP separation.

## Bounded experiment, independent audit and reproducibility

Implementation: [certificate constructor](../experiments/generic_gate_miter_resolution.py). Independent validation: [separate signed-literal-set checker](../tests/test_generic_gate_miter_resolution.py), which never calls the constructor's resolver. Stored [deterministic report](../results/generic_gate_miter_resolution.json) contains complete certificate SHA-256 hashes for four small circuit DAGs and five seeded 12-gate DAGs (seeds 29, 31, 37, 41, 43). No randomized hypothesis search was used.

| Case | gates | input clauses | derived ordinary-resolution lines | preregistered bound |
| --- | ---: | ---: | ---: | ---: |
| small 1: AND | 1 | 8 | 6 | 10 |
| small 2: AND then OR with fanout | 2 | 14 | 12 | 18 |
| small 3: XOR, NOT, AND | 3 | 20 | 20 | 28 |
| small 4: AND, OR, XOR, NOT | 4 | 26 | 30 | 36 |
| seeded 29 | 12 | 68 | 70 | 88 |
| seeded 31 | 12 | 64 | 56 | 78 |
| seeded 37 | 12 | 74 | 88 | 104 |
| seeded 41 | 12 | 74 | 82 | 104 |
| seeded 43 | 12 | 70 | 74 | 94 |

For all nine cases, the independent checker replays every parent pair, pivot, resulting signed-literal set and final empty clause, checking width at most three. The test also intentionally corrupts a pivot, forward parent, derived clause and input literal; all four are rejected. The four small cases use at most 1024 full Boolean assignments each; independent literal evaluation finds no satisfying assignment to an opposed miter. For every primary-input assignment in these small circuits, evaluating the gate DAG gives an explicit satisfying extension for the **same-output** sibling (choosing the output polarity matching that particular assignment). These controls establish nonvacuous, definition-correct gate encodings without claiming that every circuit outputs 1 somewhere. The test rejects invalid gate arity, self-operand binary gates, forward references and an empty circuit.

Reproduce:

```bash
python experiments/generic_gate_miter_resolution.py --out /tmp/generic_gate_miter_resolution.json
python -m unittest discover -s tests -p test_generic_gate_miter_resolution.py -v
python scripts/reproduce.py --out-dir reproduced --check
```

The saved report does not contain full proofs; the deterministic generator reconstructs them and the test independently checks their syntax and the hash of each. The report is not a formal proof in Lean. The mathematical theorem's universally quantified part is **paper reasoning plus a uniform explicit certificate scheme**. The finite Python tests do not themselves prove it. Existing Lean checks verify pre-existing theorems only.

## Result and next falsifier

**H survived the predeclared bounded tests**, but this is a *negative transfer result*: any model-independent claim that the internal computational complexity of a function automatically forces a large ordinary-resolution proof for a two-copy **identical-circuit** opposite-output miter is false, because every such miter has a linear-size DAG resolution proof. Even an arbitrarily shared, nonlinear original circuit does not change this argument. This does not apply if two circuits are functionally equivalent but syntactically unrelated, or if one copy is absent.

**Next distinct test:** define an asymmetric miter where two *different* circuit encodings are equivalent, and investigate whether a local equivalence correspondence is actually provable, or whether its absence invalidates gate-by-gate charging. Pre-register explicit structural assumptions and try a syntactically different but semantically equivalent pair first; do not enlarge the existing affine-flat or CNF truth-table caps. More generally, pursuing P≠NP requires hard UNSAT families and lower bounds that quantify over every correct algorithm, not over this provably easy equality special case. No P=NP or P≠NP proof was obtained.



### Reproduction-gate failure and repair

Intermediate branch CI before the fixed report was committed correctly failed because the new unit test could not find `results/generic_gate_miter_resolution.json`. After the report existed, the global reproduction gate still rejected `results/RUN_SUMMARY.json`: our first metadata edit had parsed and rewritten the **entire** JSON through JavaScript, silently rounding preexisting integer values above 2^53 (for example `18446744073709551551`). This was a *metadata serialization error*, not an invalid resolution step. The corrective commit starts from the exact main JSON **text**, changes the test count from 411 to 416 and inserts only two source hashes without parsing large integers. This preserves every prior numerical fact. The standalone five new tests had already passed independently, and all 416 unittest cases passed before the summary comparison. Only the final latest-head complete CI is an acceptable reproducibility verdict, not the earlier failing intermediary commits.
