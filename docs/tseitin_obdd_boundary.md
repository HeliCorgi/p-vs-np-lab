# Phase 27 preregistration: ordered DAGs versus exact Tseitin affine covers

Date: 2026-11-08 JST. Starting main: `5a37d5b6eb7467d40355e4734660d46300d53c00`; previous completed PR #4. No open PRs, no newer main workflow changes at the start.

## Falsifiable hypotheses and independent gates (registered before coding)

The phase-26 relation `T_m` is the satisfying assignment set of its explicit AND/XOR Tseitin 3-CNF, with (4m-1) Boolean variables, (7m-3) clauses, and exact affine one-cover number (2^m-1).

- **H1, negative transfer gate.** Contrary to a naive proposed size lower bound (\text{OBDD nodes}\ge c_{\rm aff}(T_m)), this same relation admits a deterministic ordered read-once decision DAG with variable order `x0,y0,p0,x1,y1,p1,t1,...`, no more than **four live states per variable level**, and no more than `12m-7` nonterminal nodes (two shared terminals excluded), for every (m\ge1). Every accepted assignment must satisfy the *entire* Tseitin CNF, not just its projection.
- **H2, order-sensitivity gate.** Under any OBDD that tests all `x` variables before any of the other variables, the cut just after the `x` block has at least (2^m-1) nonreject residual states. This lower bound must apply to the same `T_m`.
- **Falsifiers.** A CNF/OBDD mismatch on a complete assignment; an incorrect width/node count; a pair of distinct nonzero `x` prefixes with identical residual Boolean functions; or a missing gate/output constraint in the read-once construction.

**Hard stop and resource budget.** Enumerate full extended Boolean inputs only for `m=1,2,3`, as in phase 26 (maximum (2^{11}=2048) assignments). Enumerate residual suffix truth vectors at these same sizes only. Do not increase the affine-flat RREF/enumeration cap, run SAT solvers on larger examples, or rerun the expensive upstream ETH Lean build. Require a mathematical induction and distinguish it from Python's finite checks. Use standard-library Python, test the gate graph against an independent raw-CNF evaluator, compare accepted-path counts by DAG dynamic programming against an independent exact expected count. Run the existing GitHub research-check and ordinary-PC gates. Abort/generalize neither H1 nor H2 if a small counterexample appears; record it instead.

**Prior art and scope.** Ordered BDDs and sharing of residual functions are classical, not a new complexity model: R. E. Bryant, *Graph-Based Algorithms for Boolean Function Manipulation*, IEEE Trans. Comput. C-35 (1986), 677–691, https://doi.org/10.1109/TC.1986.1676819 ; A. Darwiche and P. Marquis, *A Knowledge Compilation Map*, JAIR 17 (2002), 229–264, https://doi.org/10.1613/JAIR.989 . The `T_m`-specific order contrast and fixed finite audit here are elementary deductions, with no novelty/priority claim.

This is a model-boundary experiment: a compact OBDD for a satisfiable explicit family does not decide arbitrary SAT and neither H1 nor H2 would establish P=NP or P≠NP.

## Outcome

Pending pre-registered tests; record failures and successful scope only after independent validation.
