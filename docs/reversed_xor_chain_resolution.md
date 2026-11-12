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

## Result of the preregistered cycle (2026-11-12 JST)

**H passed.** This is an *explicit linear-size ordinary-resolution upper bound for one special UNSAT family*, not a complexity lower bound. For every `m>=1`, the source CNF has exactly `3m+2` Boolean variables, `8m+4` input clauses, and a strict width-at-most-three, `10m-2`-inference DAG refutation (source clauses are not counted as inferences). It is **not** claimed to be a minimum-size proof. The all-size mathematical proof is given below; finite independent verification is separate.

### Mathematical proof

For each `i=0,...,m-1`, use the standard four 3-clauses for the truth table of `c=a XOR z` with `a=p_i,z=x_i,c=p_(i+1)`, and four more for `b=z XOR d` with `b=s_i,d=s_(i+1)`. Each source clause excludes exactly one falsifying local input triple. The four source units are `-p_0,-s_m,+p_m,-s_0`. Notice that the *two output* units demand opposite parity: the first chain starts at zero and ends at one; the second ends at zero and starts at zero.

Over the two-element field,
`p_(i+1)+s_(i+1)=(p_i+x_i)+(s_i+x_i)=p_i+s_i`.
Since `p_0=s_0=0`, induction implies `p_m=s_m`, contradicting `p_m=1,s_m=0`. This proves UNSAT without an experiment, but not yet the claimed resolution resource bound.

For the resource bound, abbreviate `a=p_i,b=s_i,z=x_i,c=p_(i+1),d=s_(i+1)`. Write `-v` for a negative literal, and concatenate literals with `|` for disjunction. The four source clauses for `c=a XOR z` are
`(a|z|-c), (a|-z|c), (-a|z|c), (-a|-z|-c)`.
The four source clauses for `b=z XOR d` are
`(z|d|-b), (z|-d|b), (-z|d|b), (-z|-d|-b)`.

At `i=0`, the units `-a` and `-b` yield the six exact ordinary-resolution inferences below. Each arrow denotes a resolution on the variable displayed in the last column.

| Line | Exact derived clause | Parents | Pivot |
|---|---|---|---|
| B1 | `-z|d` | `-b`, `b|-z|d` | `b` |
| B2 | `z|-c` | `-a`, `a|z|-c` | `a` |
| B3 | `-c|d` | B1, B2 | `z` |
| B4 | `z|-d` | `-b`, `b|z|-d` | `b` |
| B5 | `-z|c` | `-a`, `a|-z|c` | `a` |
| B6 | `c|-d` | B4, B5 | `z` |

For every `i>=1`, assume the two clauses `E1=(-a|b)` and `E2=(a|-b)` have already been derived. The following **ten** exact binary resolutions derive `(-c|d)` and `(c|-d)` for the next boundary. None is a weakening or an extra axiom.

| Line | Exact derived clause | Parents | Pivot |
|---|---|---|---|
| T1 | `-c|-z|-b` | E2, `-a|-z|-c` | `a` |
| T2 | `-c|-b|d` | T1, `-b|z|d` | `z` |
| T3 | `-c|b|z` | E1, `a|z|-c` | `a` |
| T4 | `-c|b|d` | T3, `b|-z|d` | `z` |
| T5 | `-c|d` | T2, T4 | `b` |
| T6 | `-b|z|c` | E2, `-a|z|c` | `a` |
| T7 | `-d|z|c` | T6, `b|z|-d` | `b` |
| T8 | `b|-z|c` | E1, `a|-z|c` | `a` |
| T9 | `-d|-z|c` | T8, `-b|-z|-d` | `b` |
| T10 | `c|-d` | T7, T9 | `z` |

The two resulting clauses are `p_(i+1)<->s_(i+1)` in CNF form. After the first six inferences and `m-1` repetitions of the ten-line template, one last resolution of `p_m` with `(-p_m|s_m)` yields the unit `s_m`; resolving with the source unit `-s_m` yields the empty clause. The derived-line count is exactly
`6+10(m-1)+2=10m-2`.
Every line is either width 2, width 3, a unit, or the empty clause. At each step, the parents are earlier lines or original source clauses, so the complete proof is a strict DAG resolution refutation of maximum width 3. This completes the all-size theorem.

**Boundary of the argument.** The intermediate states `p_i` and `s_i` are *not* unconditionally equivalent functions of the shared inputs. For `m=2` and `(x_0,x_1)=(1,0)`, `p_1=1` but `s_1=0`. Their derived equality is conditional on the opposite output assumption. Thus the theorem genuinely differs from identical-gate or pointwise De Morgan rewriting proofs in PRs #8/#10, but is a structured cancellation result rather than an arbitrary equivalence-miter theorem. A chain reversal has a path-like boundary and shares each input at the same induction step; an arbitrary permutation need not.

### Independent computational evidence

The deterministic generator `research/reversed_xor_chain/generate.py` emits original source clauses and a literal-by-literal resolution sequence. The **separate** `research/reversed_xor_chain/audit.py` independently reconstructs source clauses by local eight-row XOR truth tables and checks every two-parent exact resolvent, positive pivot, earlier-parent indices, all widths, and final empty clause. It does not invoke the generator's resolution helper. Four deliberately malformed certificates (source axiom, pivot, parent index, resolvent) are all rejected.

Only the preregistered sizes `m=1,2,3,5,8` were run. Counts of derived lines were respectively **8, 18, 28, 48, 78** (exactly the all-size expression), totaling 180 derived lines and 172 source lines. Exhaustive total-CNF assignments were checked at `m=1,2,3` only: `32+256+2048=2336` assignments, all UNSAT. The aligned-output sibling is shown SAT by an explicit gate-consistent model in every sampled case. Fixed SHA-256 digests of complete generated proof lists are saved in [the report](../results/reversed_xor_chain.json); no larger search was needed.

Reproduce using only Python standard library:

```bash
python3 research/reversed_xor_chain/audit.py --check
python3 research/reversed_xor_chain/generate.py
```

The isolated [CI workflow](../.github/workflows/reversed-xor-chain.yml) reruns the full independent audit and compares the exact saved report. The existing repository-wide Python and Lean checks remain separate and have no new Lean endpoint in this cycle. Passing a finite replay is **not** a Lean proof of the universal theorem; the latter is the explicit induction and resolution templates above.

### Failure analysis and next falsifier

The tempting claim that radically different intermediate computation order forces superlinear ordinary-resolution proofs is refuted even without any gate-to-gate syntactic alignment: reverse-prefix parity has a 3-width, linear proof. The correct resource is a *specific common boundary invariant*, not textual gate alignment. Neither this result nor its finite checks imply a uniform polynomial-time algorithm for arbitrary UNSAT or a superpolynomial lower bound for general SAT.

Next preregistered adversarial direction: hold the same XOR-chain functionality fixed but permute the right-chain order by a non-reversal permutation, so the same `x_i` no longer appears in both local gates of one induction step. Determine whether an explicit bounded-width invariant exists, or exhibit a small certified failure for the **particular** local ten-line transfer. Then ask which structural parameter (e.g. cutwidth/treewidth of the paired incidence graph) quantitatively governs proof width, before any attempt at an all-algorithm complexity claim. Do not merely increase the current finite search cutoff.

**Evidence distinctions:** Universal UNSAT and the precise width/line bound are proved by the displayed mathematical construction; Python and CI independently replay five finite proof instances and check small complete Boolean spaces; there is **no new Lean formalization** and **no P=NP or P!=NP proof**. Published work on resolution width and Tseitin treewidth motivates the resource measurement but does not make this model-specific derivation a new priority claim.
