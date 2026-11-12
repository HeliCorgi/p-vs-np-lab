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


## Outcome: H holds, with an explicit all-size mathematical proof

For each original circuit wire w, let A(w)=w be the original numbered wire,
and let B(w) be the final output q of its B gadget (or w for a primary input).
Every gate is represented by its fresh A-output p and four B wires
s,t,r,q. All underlying function values agree because

\[
q=\neg(\neg u\lor\neg v)=u\land v\quad\text{(original AND)},\qquad
q=\neg(\neg u\land\neg v)=u\lor v\quad\text{(original OR)}.
\]

Inductively derive the two ordinary CNF clauses

\[
E_w^+=(\neg A(w)\lor B(w)),\qquad
E_w^-=(A(w)\lor\neg B(w))
\]

for every completed output wire. For an original primary input the equality
is syntactic: both sides use the same variable, so no lemma is needed.

**Ordinary transport, at most four resolutions per gate.** If a gate consumes
an earlier output a whose B representation is u, the already-derived
E^-=(a∨¬u) lets us resolve (s∨u) into (s∨a). Likewise
E^+=(¬a∨u) lets us resolve (¬s∨¬u) into (¬s∨¬a).
The same applies to the second input b (B representation v, new B wire t).
If an input is primary, its two source clauses are already in this form.
We now have the four clauses

\[
S_+=(s\lor a),\ S_-=(\neg s\lor\neg a),\
T_+=(t\lor b),\ T_-=(\neg t\lor\neg b).
\]

All of these are *derived ordinary lines*, not added input assumptions.
For the local proofs below write \(\Rightarrow_x\) for one ordinary binary
resolution step on pivot x; adjacent expressions are whole resolvents.
Every unused clause is an original source clause.

### AND gate: 11 local steps

The A clauses are

\[
(\neg p\lor a),\quad(\neg p\lor b),\quad(p\lor\neg a\lor\neg b).
\]

The B gadget is s=¬u, t=¬v, r=s∨t, q=¬r. The OR-gate clauses are
(r∨¬s), (r∨¬t), (¬r∨s∨t); the final NOT clauses are
(q∨r), (¬q∨¬r).

To obtain E+=(¬p∨q), make the following five resolutions:

\[
\begin{aligned}
(\neg r\lor s\lor t), S_-&\Rightarrow_s(\neg r\lor t\lor\neg a),\\
\quad T_-&\Rightarrow_t(\neg r\lor\neg a\lor\neg b),\\
\quad(q\lor r)&\Rightarrow_r(q\lor\neg a\lor\neg b),\\
\quad(\neg p\lor a)&\Rightarrow_a(q\lor\neg p\lor\neg b),\\
\quad(\neg p\lor b)&\Rightarrow_b(q\lor\neg p).
\end{aligned}
\]

To obtain E^-=(p∨¬q), make the following six resolutions:

\[
\begin{aligned}
(\neg q\lor\neg r),(r\lor\neg s)&\Rightarrow_r(\neg q\lor\neg s)
 \ \Rightarrow_{s,S_+}(\neg q\lor a),\\
(\neg q\lor\neg r),(r\lor\neg t)&\Rightarrow_r(\neg q\lor\neg t)
 \ \Rightarrow_{t,T_+}(\neg q\lor b),\\
(p\lor\neg a\lor\neg b),(\neg q\lor a)&\Rightarrow_a
(p\lor\neg b\lor\neg q)
 \ \Rightarrow_{b,(\neg q\lor b)}(p\lor\neg q).
\end{aligned}
\]

Thus one AND uses at most 4 transports plus 5+6 local resolutions = **15**.

### OR gate: 10 local steps

The A clauses are (p∨¬a), (p∨¬b), (¬p∨a∨b).
The B gadget uses r=s∧t, with clauses (¬r∨s), (¬r∨t),
(r∨¬s∨¬t); its final NOT clauses are the same (q∨r),(¬q∨¬r).

For E+=(¬p∨q), first derive (¬r∨¬a) from (¬r∨s),S_- and
(¬r∨¬b) from (¬r∨t),T_-. Resolve the former with
(¬p∨a∨b), then the latter, obtaining (¬p∨¬r).
Resolve with (q∨r) to get (¬p∨q). This is **five** resolutions.

For E^-=(p∨¬q), resolve (¬q∨¬r) with (r∨¬s∨¬t),
then S_+, then T_+, producing (¬q∨a∨b).
Resolve successively with (p∨¬a) and (p∨¬b) to obtain
(p∨¬q). This is another **five** resolutions.

Thus one OR uses at most 4 transports plus 5+5 local resolutions = **14**.
Every source and derived clause in both templates has width at most 3.

### Induction and final contradiction

The predecessor-equality clauses for a gate are available because the original
circuit is acyclic and topologically indexed. Inductively the two output
equalities are derived for *all* gates, irrespective of fanout or how often a
completed output is reused. This is a DAG proof: previously derived clauses
are reused without rederiving them.

For the final A-output p and B-output q, resolve the original output unit (p)
with (¬p∨q) to get (q), then resolve with the original opposite unit (¬q)
to obtain the **empty clause**. These are exactly two final steps.

There are g A-gate variables, 4g B-gate variables, and n shared inputs:
**n+5g variables**. There are 3g original gate clauses, 9g B-gadget clauses,
and 2 opposite output units: **12g+2 source clauses**. All local resolutions
are strict binary resolution. The step-count inequality is therefore

\[
\boxed{S\le 15A+14O+2,\qquad\text{width}\le 3}.
\]

The constructed proof has O(g) lines of constant width. Explicit wire IDs
and line indices use O(log(n+g)) bits, so writing and verifying its full
certificate costs polynomial bit time in the specified input circuit size.
This is a constructive mathematical proof for the stated circuit class,
not just a finite-experiment extrapolation.

## Reproducible experiment and *independent* check

New code is isolated under `research/asymmetric_demorgan_miter/`, to avoid
conflicting with the **open** PRs #8 and #9 and the shared
`results/RUN_SUMMARY.json`. No existing experiment bounds, Lean files or
baseline source hashes were changed.

Run with Python >=3.10 and no third-party dependency:

```bash
python research/asymmetric_demorgan_miter/asymmetric_demorgan_miter.py \
  --out /tmp/asymmetric_demorgan_miter.json
python research/asymmetric_demorgan_miter/asymmetric_demorgan_audit.py \
  --output /tmp/asymmetric_demorgan_miter_audit.json --check
python -m json.tool /tmp/asymmetric_demorgan_miter.json >/dev/null
```

Compare the two generated JSON files with
`results/asymmetric_demorgan_miter.json` and
`results/asymmetric_demorgan_miter_audit.json`.
The generator emits SHA-256 digests of the *entire regenerated proof sequence*
(not of a mere status flag). The checker uses its own signed-literal-set
resolution replay, derives the expected Tseitin source clause **multiset**
independently from local prime implicates and truth tables, checks a
functional gate extension on every primary input, and rejects corrupted
pivots, parent references, conclusions and input axioms.

The preregistered six concrete DAGs plus five deterministic ten-gate DAGs
produced **832 strictly checked derived lines**, all of width at most three.
The separate semantic evaluator covered **136 primary-input assignments**;
for the two one-gate miters only it additionally enumerated **256 complete
CNF assignments**. The four malformed-proof controls were rejected.
Largest sampled case: ten gates, 54 variables, 122 source clauses; no larger
Boolean or affine search was needed. See both stored reports for case-by-case
counts and proof hashes. The universal statement is established by the
above symbolic templates and induction; finite checks audit the
implementation, not the general theorem.

**Verification boundary.** This cycle adds no Lean endpoint and makes no
claim of new Lean formalization. The dedicated `.github/workflows/asymmetric-demorgan.yml` runs the
independent audit with `--check` and compares both committed reports.
The pre-existing Python and Lean workflows remain separate checks. Independent verification of the new
certificate is the separately runnable `asymmetric_demorgan_audit.py`,
whose finite pass counts are recorded. No external specialist review or
priority claim is made.

## Failure of the proposed hardness transfer, and next falsifier

H survived its preregistered falsifiers. It gives a broader **negative**
transfer example than a syntactically identical pair: even for two
different gate-level circuit descriptions of the same Boolean function,
the opposed-output miter can admit a linear-size width-3 ordinary-resolution
proof, provided a *local correspondence* is known. Therefore an argument
charging all equivalence miters for the complexity of their represented
function must explicitly exclude or charge this kind of local rewrite.

The next genuinely different falsifier is a pair of equivalent circuits
for which no common output-wire correspondence or bounded-size local rewrite
certificate is supplied. Investigate whether a proof-translation step
requires solving the original circuit equivalence problem, and charge that
discovery rather than treating it as free. Keep the current resource cutoff;
do not increase brute-force search size. Neither an all-3-SAT polynomial-time
algorithm nor an all-algorithm lower bound is obtained. **P=NP and P≠NP
remain unproved.**
