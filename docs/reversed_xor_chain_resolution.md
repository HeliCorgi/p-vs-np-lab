# Phase 31 preregistration — reversed XOR-chain miter (2026-11-12 JST)

Base main: `3f575faccfcf11b6c25c334c0c7e46aedc946d00`.
The README, `docs/reverse_engineering.md`, `docs/solution_criteria.md`, recent main commits, and active pull requests #8 (identical mixed-gate miters), #9 (MCSP reconstruction), #10 (De Morgan rewrite) were checked before this cycle. The last three PRs remain untouched. Existing phase 28–30 certificates cover aligned circuit copies and locally known rewrites, not two **oppositely ordered XOR chains** with nonaligned intermediate gates.

## Falsifiable proposed theorem

For every integer `m >= 1`, use `m` shared Boolean inputs `x_0,...,x_(m-1)`, forward states `p_0,...,p_m`, and backward states `s_0,...,s_m`, all distinct variables. Encode `p_(i+1) = p_i XOR x_i` and `s_i = x_i XOR s_(i+1)` using **four 3-CNF clauses each**. Add the four units `not p_0`, `not s_m`, `p_m`, `not s_0`. The two chains compute the same parity of the input bits but with opposite processing order. Hypothesis H: this exact unsatisfiable CNF (with `3m+2` variables and `8m+4` input clauses) has a strict two-parent ordinary-resolution refutation with **exactly `10m-2` derived lines**, width at most 3, *without* weakening, oracle equality lemmas or added definitions. The intended proof propagates conditional equalities `p_i=s_i` from `p_0=s_0=0`, with a fixed six-line first step and ten-line local step per subsequent input, then two final resolutions.

Falsifiers: a satisfying total assignment, an incorrect input clause encoding, a single invalid resolution parent/pivot/resolvent, an omitted goal equality, an incorrect count/width, or violation of the all-size index invariant.

## Bounded tests and stop conditions

- Construct the universal local templates by complete **constant-size** clause reasoning, then instantiate them for exactly `m in {1,2,3,5,8}`.
- Independently rederive each source XOR clause from the three-bit truth table and replay every resolution using a different signed-set checker (not the proof generator's resolution helper). Reject four deliberate corruptions of the certificate.
- Exhaustively check full CNF assignments only for `m=1,2,3`, at most `2^11=2048` valuations for a case. Check the aligned-output sibling is satisfiable using an explicit model for every chosen m.
- Stop upon a falsifier; record a counterexample and retract the claim. Do not increase m or the truth-table cutoff to disguise failure. If passing, write an exact paper proof, deterministic source/proof digests, independent checker, and their scope. No Lean endpoint is promised this cycle.

The main goal remains **P=NP or P≠NP with all-input quantifiers**; this model-specific upper bound is only an adversarial gate to avoid an invalid proof-complexity transfer. In particular, a small refutation of these easy equivalent-chain miters does not prove tractability of circuit equivalence or SAT.

## Primary-source checks

- Ben-Sasson and Wigderson, *Short proofs are narrow — resolution made simple*, JACM 48(2) (2001), DOI 10.1145/375827.375835 (resolution width/size).
- Atserias and Dalmau, *A combinatorial characterization of resolution width*, JCSS 74(3) (2008), DOI 10.1016/j.jcss.2007.06.025.
- de Colnet and Mengel, *Characterizing Tseitin-formulas with short regular resolution refutations*, arXiv:2103.09609 (2021), treewidth-based complexity context.

These precedents are not evidence of priority for the proposed explicit ten-line transfer. No novelty is claimed.
