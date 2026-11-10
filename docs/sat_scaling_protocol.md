# Finite-size SAT protocol — 2026-11-07 JST

This protocol is fixed before the main sample is run. A separate pilot used
seed `19091+n` at n=24,48,72 solely to choose feasible sizes and work caps.
Those formulas do not enter the main sample. This is an exploratory local
record, not an externally preregistered study or a test of P=NP versus P≠NP.

The new user goal explicitly permits empirical tendencies as well as a
complete proof. We interpret a tendency as growth of a specified algorithm
on a specified input distribution. We do not interpret a regression score
as a probability that a complexity-class separation is true.

* Uniform random proper 3-CNF without replacement, m=floor(4.25n) and m=6n.
  Sizes: 12,18,24,30,36,42,48,54,60 variables. Fit on the first six sizes;
  predict the last three. The two densities are different distributions,
  not SAT/UNSAT labels fixed in advance.
* A tractable negative control: a connected cubic graph made from a cycle
  plus a disjoint uniformly sampled perfect matching. Vertices carry
  random charges with odd total parity. Each degree-three parity equation
  is encoded by its four forbidden-word clauses. Sizes (edge variables):
  12,15,18,21,24,27,30,33. Fit on the first five; predict the last three.
  These formulas are UNSAT by summing all equations over GF(2).
* Sixteen deterministic independent-seed replicates per family/size.
  Seed = first 16 hexadecimal digits of SHA256 of
  `sat-scaling-v1:family:n:replicate`. Each algorithm sees the same formulas.
* Two elementary complete DPLL algorithms, with unit propagation and either
  lowest-index/positive branching or occurrence-based branching in shortest
  clauses. No learning, restarts, symmetry detection, or claim of competitive
  performance with modern SAT solvers.
* Count inspected literals in propagation and branching, plus nodes,
  decisions and propagations. Literal counts are a work proxy, not total
  bit time or wall-clock time. Input validation, certificate replay and
  some bookkeeping are outside this count. Store actual DIMACS byte lengths.
* Work caps: 2,000,000 literal inspections for random formulas, 8,000,000
  for the XOR control. Exhaustion means UNKNOWN, never UNSAT. Keep every
  unfinished case as right-censored; never fit only completed instances.
* Summary response: the upper central order statistic (9th of 16) of work.
  It is exact when that position belongs to a completed run; otherwise it
  is a lower bound. Do not fit a series with any non-exact median. Also
  report 25th/75th nearest-rank order statistics and all answer counts.
* Fit equal-parameter models to log2(work+1): `a+b log2(n)` (polynomial),
  `a+b sqrt(n)` (subexponential), `a+bn` (exponential). Choose by held-out
  log2 RMSE, not training error. Repeat with the two smallest training
  sizes removed, using the same holdout, to expose window sensitivity.
  No model-class winner is a complexity-class verdict.
* Independently check every returned SAT assignment on the input CNF.
  Replay every DPLL UNSAT certificate using original unit-clause reasons,
  both branch assignments and false input clauses at leaves. Test small
  cases against exhaustive assignment enumeration.
* Recover the XOR equations from complete parity blocks in the actual CNF
  without hidden generator metadata. Solve by Gaussian elimination and
  check the XOR sum yielding `0=1`. Report row operations separately from
  DPLL's literal counts; the two counters are not interchangeable.

The graph control is essential: a steep DPLL curve on a polynomial-time
fragment demonstrates why the same curve on random SAT cannot establish a
lower bound for every algorithm. SAT/UNSAT mixtures and size-dependent
satisfiability rates are retained in the report; these medians are neither
worst-case complexity nor a controlled estimate of conditional UNSAT cost.

For the proof objective, success still means a uniform all-input polynomial
SAT algorithm or an all-algorithm superpolynomial lower bound. A measured
exponential trend does not exclude a later crossover or a different fast
algorithm; measured polynomial growth cannot exclude rare hard instances.
No finite list of benchmark answers determines either alternative.
