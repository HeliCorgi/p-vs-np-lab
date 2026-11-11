# Phase 30: asymmetric De Morgan circuit miters — preregistered test

Date: 2026-11-11 JST. Base: main `3f575faccfcf11b6c25c334c0c7e46aedc946d00`.

## Starting status and isolation

Before selecting the test, inspected main and README, `docs/reverse_engineering.md`, `docs/solution_criteria.md`, recent commits and CI, and open PRs #8 (generic identical-circuit miters, green) and #9 (MCSP witness selection, draft, green). These are not merged and this cycle will not change either branch. The new target is **not** another MCSP circuit search, nor a copy of the syntactically-identical result. Main still carries the research-program cautions against extending a proof-system upper bound to all SAT decision algorithms.

## Falsifiable hypothesis H, fixed before implementation

Let C be any topologically indexed Boolean DAG with n>=2 distinct primary input variables, g>=1 fresh gates, binary gate type AND or OR, and *distinct* predecessor wires at each gate. Fanout and sharing are arbitrary and the designated output is the last gate. Build A as the usual three-clause-per-gate functional Tseitin encoding. Build B from the **different circuit** in which each gate on B predecessor wires u,v is replaced by the four new, fresh gate wires

    s = NOT u; t = NOT v; r = DUAL(s,t); q = NOT r,

where DUAL is OR for an original AND, and AND for an original OR. B successor gates consume q. Share only the n primary inputs; A and B have disjoint auxiliary wires. Require A's output to be true and B's output to be false.

**H:** for every admissible DAG, the resulting miter is UNSAT and has a strict, two-parent, ordinary-resolution **DAG** refutation of width at most three and at most `15 A + 14 O + 2` derived lines (A and O are numbers of original AND and OR gates). The miter has exactly `n+5g` variables and `12g+2` input clauses. Parent clauses may be shared; no weakening, semantic inference, extended-resolution rule or new axiom is permitted.

**Falsifiers:** a wrong truth-functional equivalence, invalid literal transport across previously derived equalities, a tautological/wide/incorrect resolvent, a wrong count, an admissible fanout DAG with no such certificate, or an independent evaluator/checker rejecting a generated certificate. Reject cycles, unknown gates, repeated binary operands and absent gates rather than silently weakening H.

## Hard cutoff and independent checks

Proof by induction from one **constant-size AND** and one **constant-size OR** local gate template plus 0/1/2 predecessor transports; no general SAT solver, no width increases, and no search-size escalation. Check at most six explicit cases and five fixed-seed DAGs of at most 10 gates. Exhaust the Boolean **primary input** truth tables only for n<=4, and exhaust *full CNF assignments* only when n+5g<=10 (<=1024). Use a separate signed-literal-set resolution checker and deliberately corrupted certificates as negative controls. If a bound fails, record the failed template rather than adjusting the cap post hoc.

## Primary literature consulted before experiment

- S. A. Cook and R. A. Reckhow, *The Relative Efficiency of Propositional Proof Systems*, J. Symbolic Logic 44(1):36–50, 1979, https://www.cs.toronto.edu/~sacook/homepage/cook_reckhow.pdf . Defines efficiency comparisons and the importance of proof-system resources; it does **not** assert this line count.
- G. S. Tseitin, *On the Complexity of Derivation in Propositional Calculus* (1968; English reprint 1983), https://doi.org/10.1007/978-3-642-81955-1_28 . Proof complexity background; our functional gate clauses and explicit resolution count are derived here, not attributed to Tseitin.
- Prior in-repository work: `docs/tseitin_resolution_miter.md` (specific inner product) and open PR #8 `docs/generic_gate_miter_resolution.md` (syntactically identical general circuits).

## Scope

Even if H succeeds for every admissible DAG, it is an **upper bound for a guaranteed-UNSAT, structurally related pair of circuits**, not a general equivalence checker, SAT algorithm, circuit-size lower bound, or proof of P=NP or P!=NP. A hypothetical hardness transfer must survive this adversarial case.
