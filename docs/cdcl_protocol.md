# CDCL continuation protocol — 2026-11-07 JST

Freeze before inspecting the main sample. The excluded pilot used seed
`29091+n` on random density-4.25 formulas at n=96,192,288 and odd graph XOR
at n=36,54,72, only to choose a feasible conflict budget. This is an
exploratory local protocol, not external preregistration.

The question is whether the previous elementary DPLL trend survives
practical clause learning, restarts, and solver-specific preprocessing.
The chosen implementations are **Glucose 4.2.1** (PySAT name `g42`) and
**CaDiCaL 1.9.5** (`cadical195`), from `python-sat==1.9.dev21`. These are
specific established implementations, not a claim to benchmark the latest
or best SAT solver. Use each wrapper's defaults, a fresh instance for each
formula, and proof logging. Do not infer the causal contribution of
learning alone from a comparison of different implementations.

1. Paired panel: all 416 unique formulas in `results/sat_scaling.json`,
   regenerated from their stored seeds and checked against their SHA256.
   Each solver receives exactly the previous input order, without labels,
   graph metadata, or planted witnesses. This includes all 22 previously
   censored DPLL runs. No solver-dependent instance selection.
2. Extended panel: 16 pseudorandom replicates at each new size, at both
   random densities 4.25 and 6, and for the graph-XOR odd-charge control.
   Random sizes: 96,144,192,240,288,336. XOR sizes: 36,48,60,72,84,96.
   Seed = first 16 hex digits of SHA256(`cdcl-audit-v1:family:n:replicate`).
   These are new instances, not extensions of individual old formulas.
3. Request a 25,000-conflict budget via `conf_budget`, then `solve_limited`.
   This is a **soft native budget**: a backend can overshoot between checks.
   Store actual counters. UNKNOWN is unfinished, never UNSAT. No hidden
   retry with a larger budget, no removal of unfinished instances.
4. Store conflicts, decisions, propagations and restarts as native counts.
   They do not equal DPLL's literal inspections or each other's units.
   There is no cross-solver speed ratio or wall-time race in this report.
5. Check every SAT model on original clauses. For every UNSAT result,
   write the emitted DRAT proof and require a zero exit code **and** an
   exact `s VERIFIED` line from independently compiled `drat-trim`, commit
   `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. A failed check aborts the audit.
   The checker is independent C software, not a Lean kernel proof.
6. Reconstruct and solve all XOR controls from CNF using the previous
   polynomial Gaussian algorithm; check the row-sum contradiction. A slow
   CDCL run on these formulas therefore cannot imply a general SAT lower
   bound. Validate both backends on small exhaustive/truth-table controls.
7. Report all statuses and the 9th order statistic out of 16 conflicts at
   each size. Since actual censoring thresholds differ, compute lower and
   upper order-statistic bounds: completed work is a point, UNKNOWN has
   upper bound infinity. Mark a median exact only when these bounds agree.
8. For each extended family/backend, compare curves using exact medians
   only if **every** size's median is exact. Train on the first three sizes;
   compare polynomial, square-root-exponential and exponential predictions
   on the last three, using the previous log2(work+1) convention. Repeat
   training on sizes two and three to expose sensitivity. With just three
   training sizes these fits are descriptive, not a statistical test.

All raw proof files and checker logs go to the chosen execution directory;
the compact saved report retains their hashes and validation flags. Rerun
the optional experiment to regenerate and independently check them. Default
stdlib reproduction checks the local source hashes and unit tests; it does
**not** execute or certify these external solver runs. Solver versions,
native binary hash, Python/platform and checker-source hash are retained.
No result is converted into a probability of P=NP or P≠NP.
